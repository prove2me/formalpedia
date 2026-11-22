-- Prove2me | solution 1 for growth_function_le_sauer_shelah
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:39:50.626794+00:00
-- url     : https://prove2.me/submissions/166d87f4-2496-4e6c-9218-450b693ee235

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
public import Theorems.Thm_card_restrict_le_sauer_shelah_bound
section
@[expose] public section
universe u v
private theorem ncard_restrictions_eq_card {X : Type u}
    (C : Finset (X → Bool)) (S : Finset X) :
    ({ f : ↥S → Bool | ∃ c ∈ (↑C : Set (X → Bool)),
        ∀ x : ↥S, c ↑x = f x } : Set (↥S → Bool)).ncard =
      (restrictConceptClass C S).card := by
  -- The set equals ↑(restrictConceptClass C S) as a Set
  have hEq : { f : ↥S → Bool | ∃ c ∈ (↑C : Set (X → Bool)), ∀ x : ↥S, c ↑x = f x } =
      ↑(restrictConceptClass C S) := by
    ext f
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, restrictConceptClass, Finset.mem_image,
      Finset.mem_coe]
    constructor
    · rintro ⟨c, hcC, hcf⟩
      refine ⟨c, hcC, funext fun ⟨x, hx⟩ => ?_⟩
      -- Goal: restrictToFinset c S ⟨x, hx⟩ = f ⟨x, hx⟩
      -- restrictToFinset c S ⟨x, hx⟩ = c x by definition
      -- hcf ⟨x, hx⟩ : c ↑⟨x, hx⟩ = f ⟨x, hx⟩, i.e. c x = f ⟨x, hx⟩
      exact hcf ⟨x, hx⟩
    · rintro ⟨c, hcC, rfl⟩
      exact ⟨c, hcC, fun ⟨x, hx⟩ => rfl⟩
  rw [hEq, Set.ncard_coe_finset]
private theorem ncard_restrictions_le_bound {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X) (d : ℕ)
    (hd : Finset.vcDim (conceptClassToFinsetFamily C) = d) :
    ({ f : ↥S → Bool | ∃ c ∈ (↑C : Set (X → Bool)), ∀ x : ↥S, c ↑x = f x } : Set _).ncard ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i := by
  rw [ncard_restrictions_eq_card]
  exact card_restrict_le_sauer_shelah_bound C S d hd
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (d : ℕ)
    (hd : Finset.vcDim (conceptClassToFinsetFamily C) = d) (m : ℕ) (_hm : d ≤ m) :
    GrowthFunction X (↑C : Set (X → Bool)) m ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by
  unfold GrowthFunction
  set B := ∑ i ∈ Finset.range (d + 1), Nat.choose m i
  -- The sSup is over Set.range of a function from { S // S.card = m } to ℕ
  -- Each value is ncard { f | ... } which we've bounded
  -- Use: sSup of a set bounded by B is ≤ B
  -- For ℕ (ConditionallyCompleteLinearOrderBot): sSup ∅ = 0 ≤ B, and if nonempty use csSup_le
  -- Use csSup_le': show B is an upper bound of the range
  apply csSup_le'
  intro n hn
  obtain ⟨⟨S, hSm⟩, rfl⟩ := hn
  change ({ f : ↥S → Bool | ∃ c ∈ (↑C : Set (X → Bool)), ∀ x : ↥S, c ↑x = f x } : Set _).ncard ≤ B
  calc ({ f : ↥S → Bool | ∃ c ∈ (↑C : Set (X → Bool)), ∀ x : ↥S, c ↑x = f x } : Set _).ncard
      ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i := ncard_restrictions_le_bound C S d hd
    _ = B := by rw [hSm]
