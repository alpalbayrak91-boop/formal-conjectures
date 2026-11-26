/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 23

*References:*
* [erdosproblems.com/23](https://www.erdosproblems.com/23)
* [OEIS A389646](https://oeis.org/A389646)
* [Balogh-Clemen-Lidicky, Max Cuts in Triangle-free Graphs](https://arxiv.org/abs/2103.14179)
* [McKay, Extremal graphs for bipartization of triangle-free graphs](https://users.cecs.anu.edu.au/~bdm/data/graphs.html)
-/

@[expose] public section

open SimpleGraph BigOperators

namespace Erdos23

open scoped Classical in
/--
Every triangle-free graph on $5$ vertices can be made bipartite by removing at most $1$ edge.
This is the $n = 1$ case of Erdős Problem 23.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1 :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  intro G hcf
  by_cases h : ∃ v x y, x ≠ y ∧ G.Adj v x ∧ G.Adj v y
  · obtain ⟨v, x, y, hxy, hvx, hvy⟩ := h
    let c : Fin 5 → Fin 2 := fun w => if G.Adj v w then 0 else 1
    let H : SimpleGraph (Fin 5) := ⟨fun a b => G.Adj a b ∧ c a ≠ c b,
      ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩, ⟨fun _ h => h.2 rfl⟩⟩
    let S : Finset (Fin 5) := {v, x, y}
    have hUcard : Sᶜ.card = 2 := by
      rw [Finset.card_compl, Fintype.card_fin]; simp [S, hvx.ne, hvy.ne, hxy]
    have hend {a b} (hab : G.Adj a b) (hnab : ¬ H.Adj a b) : ({a, b} : Finset (Fin 5)) = Sᶜ := by
      have hcab : c a = c b := by_contra fun hne => hnab ⟨hab, hne⟩
      have hva : ¬ G.Adj v a := fun hva => by
        have hvb : G.Adj v b := by by_contra hvb; simp [c, hva, hvb] at hcab
        exact hcf {v, a, b} (is3Clique_triple_iff.2 ⟨hva, hvb, hab⟩)
      have hvb : ¬ G.Adj v b := fun hvb => by simp [c, hva, hvb] at hcab
      refine Finset.eq_of_subset_of_card_le (fun u hu => Finset.mem_compl.2 fun huS => ?_)
        (by rw [hUcard, Finset.card_pair hab.ne])
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hu huS
      rcases hu with rfl | rfl <;> rcases huS with rfl | rfl | rfl
      exacts [hvb hab, hva hvx, hva hvy, hva hab.symm, hvb hvx, hvb hvy]
    refine ⟨H, fun _ _ h => h.1, ⟨Coloring.mk c fun h => h.2⟩,
      Finset.card_le_one.2 fun e₁ he₁ e₂ he₂ => ?_⟩
    induction e₁ using Sym2.ind with | _ a₁ b₁ => ?_
    induction e₂ using Sym2.ind with | _ a₂ b₂ => ?_
    simp only [Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet] at he₁ he₂
    have hp := (hend he₁.1 he₁.2).trans (hend he₂.1 he₂.2).symm
    have ha₁ : a₁ = a₂ ∨ a₁ = b₂ := by simpa using Finset.ext_iff.1 hp a₁
    have hb₁ : b₁ = a₂ ∨ b₁ = b₂ := by simpa using Finset.ext_iff.1 hp b₁
    rcases ha₁ with rfl | rfl <;> rcases hb₁ with rfl | rfl
    exacts [absurd rfl he₁.1.ne, rfl, Sym2.eq_swap, absurd rfl he₁.1.ne]
  · refine ⟨G, le_rfl, ⟨Coloring.mk (fun v => if ∃ w, G.Adj v w ∧ v < w then 0 else 1) ?_⟩,
      by simp⟩
    intro a b hab
    have huniq {u w₁ w₂} (h₁ : G.Adj u w₁) (h₂ : G.Adj u w₂) : w₁ = w₂ :=
      by_contra fun hne => h ⟨u, w₁, w₂, hne, h₁, h₂⟩
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · rw [if_pos ⟨b, hab, hlt⟩, if_neg fun ⟨w, hw, hw'⟩ =>
        lt_asymm hlt (huniq hw hab.symm ▸ hw')]; decide
    · exact absurd rfl hab.ne
    · rw [if_neg fun ⟨w, hw, hw'⟩ => lt_asymm hgt (huniq hw hab ▸ hw'),
        if_pos ⟨a, hab.symm, hgt⟩]; decide

open scoped Classical in
/--
There exists a triangle-free graph on $5$ vertices such that at least $1$ edge must be removed
to make it bipartite. This shows the bound in `erdos_23_n1` is tight.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1_tight :
    ∃ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 5)),
        H ≤ G → H.IsBipartite → 1 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  -- The `5`-cycle is triangle-free, and a bipartite subgraph missing no edge would be the
  -- `5`-cycle itself, which has chromatic number `3`.
  refine ⟨cycleGraph 5, by unfold CliqueFree; decide +kernel, fun H hHG hH => ?_⟩
  by_contra hcon
  have h0 := Finset.card_eq_zero.1 (Nat.lt_one_iff.1 (not_le.1 hcon))
  have hsub := Finset.sdiff_eq_empty_iff_subset.1 h0
  rw [Finset.subset_iff] at hsub
  simp only [mem_edgeFinset] at hsub
  have hGH : cycleGraph 5 ≤ H := edgeSet_subset_edgeSet.1 fun _ he => hsub he
  obtain rfl : H = cycleGraph 5 := le_antisymm hHG hGH
  have h2 := hH.chromaticNumber_le
  rw [chromaticNumber_cycleGraph_of_odd 5 (by norm_num) (by decide)] at h2
  exact absurd h2 (by decide)

open scoped Classical in
/--
Every triangle-free graph on $25$ vertices can be made bipartite by removing at most $25$
edges.

This is the $n = 5$ case of Erdős Problem 23.  It follows from the high-density range of
Balogh-Clemen-Lidicky together with McKay's complete catalogue of the 23-vertex extremal
graphs for bipartization of triangle-free graphs.
-/
@[category research solved, AMS 5]
theorem erdos_23.variants.n5 :
    ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 25)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  sorry

/--
The blow-up of the 5-cycle $C_5$: replace each vertex of $C_5$ with an independent set of $n$
vertices, and connect two vertices iff their corresponding vertices in $C_5$ are adjacent.
The vertex set is $\mathbb{Z}/5\mathbb{Z} \times \{0, \ldots, n-1\}$, where $(i, a)$ and $(j, b)$
are adjacent iff $j = i + 1$ or $i = j + 1$ in $\mathbb{Z}/5\mathbb{Z}$.
-/
def blowupC5 (n : ℕ) : SimpleGraph (ZMod 5 × Fin n) :=
  SimpleGraph.fromRel fun (i, _) (j, _) => i + 1 = j ∨ j + 1 = i

open scoped Classical in
/--
The blow-up of $C_5$ shows that the bound $n^2$ in Erdős Problem 23 is tight:
any bipartite subgraph must omit at least $n^2$ edges.
-/
@[category test, AMS 5]
theorem blowupC5_tight (n : ℕ) (_hn : 0 < n) (H : SimpleGraph (ZMod 5 × Fin n))
    (hH : H ≤ blowupC5 n) (hBip : H.IsBipartite) :
    n ^ 2 ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card := by
  let _ := hH; obtain ⟨c⟩ := hBip
  let A (i : ZMod 5) := (Finset.univ : Finset (Fin n)).filter fun x => c (i, x) = 0
  let S := (Finset.univ : Finset (ZMod 5)).sigma fun i => A i ×ˢ A (i + 1) ∪ (A i)ᶜ ×ˢ (A (i + 1))ᶜ
  let f : (i : ZMod 5) × (Fin n × Fin n) → Sym2 (ZMod 5 × Fin n) :=
    fun ⟨i, x, y⟩ => s((i, x), (i + 1, y))
  have hf : Function.Injective f := by
    rintro ⟨i, x, y⟩ ⟨j, x', y'⟩ h; rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · cases h1; cases h2; rfl
    · injection h1 with hi _; injection h2 with hj _
      exact False.elim ((by decide : ∀ a b : ZMod 5, a = b + 1 → a + 1 = b → False) i j hi hj)
  have hsub : S.image f ⊆ (blowupC5 n).edgeFinset \ H.edgeFinset := by
    intro e he; obtain ⟨⟨i, x, y⟩, hmem, rfl⟩ := Finset.mem_image.1 he
    rw [Finset.mem_sdiff, mem_edgeFinset, mem_edgeFinset, mem_edgeSet, mem_edgeSet]
    refine ⟨⟨fun h => (by decide : ∀ a : ZMod 5, a ≠ a + 1) i (congrArg Prod.fst h),
      Or.inl (Or.inl rfl)⟩, fun hadj => ?_⟩
    simp only [S, A, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_product, Finset.mem_compl, Finset.mem_filter] at hmem
    have := c.valid hadj; rcases hmem with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
  have hsum (i : ZMod 5) : (((A i)ᶜ).card : ℤ) = (n : ℤ) - (A i).card := by
    have := (A i).card_le_univ; rw [Finset.card_compl, Fintype.card_fin] at *; omega
  have halg : (n : ℤ) ^ 2 ≤ ∑ i : ZMod 5,
      (((A i).card : ℤ) * (A (i + 1)).card + (((A i)ᶜ).card : ℤ) * ((A (i + 1))ᶜ).card) := by
    let a (i : ZMod 5) : ℤ := (A i).card; let b (i : ZMod 5) : ℤ := ((A i)ᶜ).card
    let g (i : ZMod 5) : ℤ := a i * a (i + 1) + b i * b (i + 1)
    let R := 2 * (a 0 * a 1 * a 4 + b 0 * b 1 * b 4 + a 1 * a 2 * b 4 +
      b 1 * b 2 * a 4 + a 2 * a 3 * a 4 + b 2 * b 3 * b 4)
    have hid : (n : ℤ) * ((∑ i : ZMod 5, g i) - (n : ℤ) ^ 2) = R := by
      rw [show (∑ i : ZMod 5, g i) = g 0 + g 1 + g 2 + g 3 + g 4 from Fin.sum_univ_five g]
      simp only [g, R, a, b, hsum, show (0 : ZMod 5) + 1 = 1 from rfl,
        show (1 : ZMod 5) + 1 = 2 from rfl, show (2 : ZMod 5) + 1 = 3 from rfl,
        show (3 : ZMod 5) + 1 = 4 from rfl, show (4 : ZMod 5) + 1 = 0 from rfl]; ring
    have : 0 ≤ R := by positivity
    have : (0 : ℤ) < n := Nat.cast_pos.2 _hn
    nlinarith
  have hScard : n ^ 2 ≤ S.card := by
    rw [Finset.card_sigma, Finset.sum_congr rfl fun i _ => by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_product.2 (Or.inl disjoint_compl_right)),
        Finset.card_product, Finset.card_product]]
    exact_mod_cast halg
  exact (hScard.trans (Finset.card_image_of_injective S hf).symm.le).trans
    (Finset.card_le_card hsub)

open scoped Classical in
/--
There exists a triangle-free graph on $25$ vertices such that at least $25$ edges must be
removed to make it bipartite.  The balanced blow-up of $C_5$ with five parts of size $5$
witnesses this.
-/
@[category research solved, AMS 5]
theorem erdos_23.variants.n5_tight :
    ∃ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 25)),
        H ≤ G → H.IsBipartite → 25 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  let e : ZMod 5 × Fin 5 ≃ Fin 25 := finProdFinEquiv
  have hcf₀ : (blowupC5 5).CliqueFree 3 := by
    intro t ht; rw [is3Clique_iff] at ht
    rcases ht with ⟨⟨i, _⟩, ⟨j, _⟩, ⟨k, _⟩, huv, huw, hvw, _⟩
    have hno : ∀ a b c : ZMod 5, ((a + 1 = b ∨ b + 1 = a) ∨ (b + 1 = a ∨ a + 1 = b)) →
        ((a + 1 = c ∨ c + 1 = a) ∨ (c + 1 = a ∨ a + 1 = c)) →
        ((b + 1 = c ∨ c + 1 = b) ∨ (c + 1 = b ∨ b + 1 = c)) → False := by decide
    exact hno i j k huv.2 huw.2 hvw.2
  refine ⟨(blowupC5 5).map e.toEmbedding,
    hcf₀.comap (Iso.map e (blowupC5 5)).symm.isContained, fun H hHG hBip => ?_⟩
  let H₀ := H.comap e.toEmbedding
  have hH₀ : H₀ ≤ blowupC5 5 := fun u v huv =>
    (map_adj_apply (G := blowupC5 5) (f := e.toEmbedding)).1 (hHG huv)
  have hBip₀ : H₀.IsBipartite := let ⟨c⟩ := hBip; ⟨Coloring.mk (c ∘ e) fun h => c.valid h⟩
  refine (blowupC5_tight 5 (by norm_num) H₀ hH₀ hBip₀).trans
    (Finset.card_le_card_of_injOn (Sym2.map e) ?_ fun _ _ _ _ h => Sym2.map.injective e.injective h)
  intro a ha; induction a using Sym2.ind with | _ u v => ?_
  simp only [Finset.mem_coe, Finset.mem_sdiff, mem_edgeFinset, Sym2.map_mk, mem_edgeSet] at ha ⊢
  exact ⟨(map_adj_apply (G := blowupC5 5) (f := e.toEmbedding)).2 ha.1, ha.2⟩

open scoped Classical in
/--
Can every triangle-free graph on $5n$ vertices be made bipartite by deleting at most $n^2$ edges?
-/
@[category research open, question, AMS 5]
theorem erdos_23 :
    ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ n^2 := by
  sorry

-- TODO: add the remaining variants/statements/comments

end Erdos23
