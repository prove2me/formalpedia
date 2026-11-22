-- Prove2me | solution 1 for empiricalMeasureError_eq_empiricalError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:18.424208+00:00
-- url     : https://prove2.me/submissions/c6d920d6-6b63-4300-a54c-9772dfd4afdf

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (h : Concept X Bool) (c : Concept X Bool)
    {m : ℕ} (hm : 0 < m) (xs : Fin m → X) :
    (EmpiricalMeasureError X h c xs).toReal =
      EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) := by
  have hm' : m ≠ 0 := by omega
  unfold EmpiricalMeasureError TrueError EmpiricalMeasure
  rw [dif_neg hm']
  unfold EmpiricalError
  rw [if_neg hm', MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.finsetSum_apply]
  simp only [MeasureTheory.Measure.dirac_apply, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
  rw [smul_eq_mul]
  have hne_top : ∀ i ∈ Finset.univ, (if h (xs i) ≠ c (xs i) then (1 : ENNReal) else 0) ≠ ⊤ := by
    intro i _; split_ifs <;> simp
  rw [ENNReal.toReal_mul, ENNReal.toReal_sum hne_top, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_natCast]
  have hsum_eq : (∑ x : Fin m, (if h (xs x) ≠ c (xs x) then (1 : ENNReal) else 0).toReal) =
      (∑ x : Fin m, zeroOneLoss Bool (h (xs x)) (c (xs x))) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold zeroOneLoss
    by_cases hd : h (xs i) = c (xs i)
    · simp [hd]
    · simp [hd, ENNReal.toReal_one]
  rw [hsum_eq]
  ring
