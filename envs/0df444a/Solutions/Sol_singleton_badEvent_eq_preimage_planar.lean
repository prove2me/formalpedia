-- Prove2me | solution 1 for singleton_badEvent_eq_preimage_planar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:41:47.350724+00:00
-- url     : https://prove2.me/submissions/ecd59186-615d-4171-876a-9bc69130e769

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_BorelAnalyticSeparation

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
theorem _root_.solution
    (A : Set ℝ) :
    singletonBadEvent A = samplePair1ToPlane ⁻¹' planarWitnessEvent A := by
  ext p
  simp only [singletonBadEvent, singletonClassOn, planarWitnessEvent, samplePair1ToPlane,
    Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨h, hh, hgap⟩
    rcases hh with rfl | ⟨a, haA, rfl⟩
    · -- zeroConcept case: gap must be 0
      exfalso
      unfold EmpiricalError zeroOneLoss zeroConcept at hgap
      simp only [show (1 : ℕ) ≠ 0 from one_ne_zero, ↓reduceIte, Fin.sum_univ_one,
        Nat.cast_one, div_one, sub_self] at hgap
      linarith
    · -- singletonConcept a case
      unfold EmpiricalError at hgap
      simp only [show (1 : ℕ) ≠ 0 from one_ne_zero, ↓reduceIte, Fin.sum_univ_one,
        Nat.cast_one, div_one] at hgap
      refine ⟨?_, ?_⟩
      · -- p.2 0 ∈ A
        by_contra h_not
        have hne : p.2 0 ≠ a := fun heq => h_not (heq ▸ haA)
        have hz : zeroOneLoss Bool (singletonConcept a (p.2 0)) (zeroConcept (p.2 0)) = 0 := by
          unfold zeroOneLoss zeroConcept singletonConcept; simp [hne]
        have hnn : zeroOneLoss Bool (singletonConcept a (p.1 0)) (zeroConcept (p.1 0)) ≥ 0 := by
          unfold zeroOneLoss; split <;> norm_num
        rw [hz] at hgap; linarith
      · -- p.1 0 ≠ p.2 0
        intro heq
        by_cases ha2 : p.2 0 = a
        · have ha1 : p.1 0 = a := heq ▸ ha2
          have e1 : zeroOneLoss Bool (singletonConcept a (p.2 0)) (zeroConcept (p.2 0)) = 1 := by
            unfold zeroOneLoss zeroConcept singletonConcept; simp [ha2]
          have e2 : zeroOneLoss Bool (singletonConcept a (p.1 0)) (zeroConcept (p.1 0)) = 1 := by
            unfold zeroOneLoss zeroConcept singletonConcept; simp [ha1]
          rw [e1, e2] at hgap; linarith
        · have e1 : zeroOneLoss Bool (singletonConcept a (p.2 0)) (zeroConcept (p.2 0)) = 0 := by
            unfold zeroOneLoss zeroConcept singletonConcept; simp [ha2]
          have hnn : zeroOneLoss Bool (singletonConcept a (p.1 0)) (zeroConcept (p.1 0)) ≥ 0 := by
            unfold zeroOneLoss; split <;> norm_num
          rw [e1] at hgap; linarith
  · rintro ⟨hmem, hne⟩
    refine ⟨singletonConcept (p.2 0), Or.inr ⟨p.2 0, hmem, rfl⟩, ?_⟩
    unfold EmpiricalError
    simp only [show (1 : ℕ) ≠ 0 from one_ne_zero, ↓reduceIte, Fin.sum_univ_one,
      Nat.cast_one, div_one]
    unfold zeroOneLoss zeroConcept singletonConcept
    simp only [↓reduceIte]
    have h1 : p.1 0 ≠ p.2 0 := hne
    simp only [h1, ↓reduceIte]
    norm_num
