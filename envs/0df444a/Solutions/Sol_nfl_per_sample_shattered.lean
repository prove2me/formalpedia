-- Prove2me | solution 1 for nfl_per_sample_shattered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:49.835571+00:00
-- url     : https://prove2.me/submissions/4647b3ae-8167-4521-9790-521c8ca824a3

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u} {C : ConceptClass X Bool}
    {T : Finset X} (hT : Shatters X C T) {m : ℕ} (hTcard : 2 * m < T.card)
    (xs : Fin m → X) (h : X → Bool) :
    ∃ c ∈ C, (∀ i : Fin m, xs i ∈ T → c (xs i) = h (xs i)) ∧
      T.card < 4 * (T.filter fun x => c x ≠ h x).card := by
  classical
  -- Define adversarial labeling: agree with h on seen points, disagree on unseen
  let f : ↥T → Bool := fun ⟨x, _⟩ =>
    if x ∈ Set.range xs then h x else !h x
  -- Shattering gives c ∈ C realizing f
  obtain ⟨c, hcC, hcf⟩ := hT f
  refine ⟨c, hcC, ?_, ?_⟩
  · -- c agrees with h on sample points that are in T
    intro i hi
    simpa only [f, Set.mem_range_self, ↓reduceIte] using hcf ⟨xs i, hi⟩
  · -- c disagrees with h on all unseen points of T
    -- So the disagreement count ≥ |T \ range(xs)| ≥ T.card - m > T.card/2
    -- First: every unseen point in T has c x ≠ h x
    have hunseen : ∀ x ∈ T, x ∉ Set.range xs → c x ≠ h x := by
      intro x hxT hxns
      have hcfx : c x = f ⟨x, hxT⟩ := hcf ⟨x, hxT⟩
      simp only [f, hxns, ↓reduceIte] at hcfx
      rw [hcfx]; cases h x <;> decide
    -- The disagreement filter contains T \ image of xs
    -- Let seen = T.filter (· ∈ range xs)
    set disagree := T.filter (fun x => c x ≠ h x) with hdisagree_def
    -- T \ (Finset.image xs Finset.univ) ⊆ disagree
    have hsub : T \ Finset.image xs Finset.univ ⊆ disagree := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and] at hx
      simp only [hdisagree_def, Finset.mem_filter]
      exact ⟨hx.1, hunseen x hx.1 (by
        intro ⟨i, hi⟩; exact hx.2 ⟨i, hi⟩)⟩
    -- |T \ image xs| ≥ T.card - m
    have hsdiff_card : T.card - m ≤ (T \ Finset.image xs Finset.univ).card := by
      have himg_le : (Finset.image xs Finset.univ).card ≤ m := by
        calc (Finset.image xs Finset.univ).card
            ≤ Fintype.card (Fin m) := Finset.card_image_le
          _ = m := Fintype.card_fin m
      -- |T \ S| + |T ∩ S| = |T| (Finset.card_sdiff_add_card_inter)
      have hkey := Finset.card_sdiff_add_card_inter T (Finset.image xs Finset.univ)
      -- |T ∩ S| ≤ |S| ≤ m
      have hinter_le : (T ∩ Finset.image xs Finset.univ).card ≤ m :=
        le_trans (Finset.card_le_card Finset.inter_subset_right) himg_le
      omega
    -- Combine: disagree.card ≥ T.card - m
    have hdisagree_ge : T.card - m ≤ disagree.card :=
      le_trans hsdiff_card (Finset.card_le_card hsub)
    -- Since 2m < T.card: T.card < 4 * (T.card - m) ≤ 4 * disagree.card
    omega
