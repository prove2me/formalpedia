-- Prove2me | solution 1 for pow_mul_exp_neg_le_factorial_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:37:33.879734+00:00
-- url     : https://prove2.me/submissions/ba2020af-8e7e-49bf-a7df-082c175bfd8b

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
theorem _root_.solution {d : ℕ} {t : ℝ} (ht : 0 < t) :
    t ^ d * Real.exp (-t) ≤ ↑((d + 1).factorial) / t := by
  have h1 : t ^ (d + 1) / ↑((d + 1).factorial) ≤ Real.exp t :=
    Real.pow_div_factorial_le_exp t ht.le (d + 1)
  have h2 : t ^ (d + 1) ≤ ↑((d + 1).factorial) * Real.exp t := by
    have := (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos (d + 1)))).mp h1
    linarith [mul_comm (Real.exp t) (↑(d + 1).factorial)]
  rw [pow_succ] at h2
  rw [le_div_iff₀ ht]
  calc t ^ d * Real.exp (-t) * t
      = t ^ d * t * Real.exp (-t) := by ring
    _ = t ^ (d + 1) * Real.exp (-t) := by rw [← pow_succ]
    _ ≤ ↑((d + 1).factorial) * Real.exp t * Real.exp (-t) := by
        apply mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.exp_pos (-t)))
    _ = ↑((d + 1).factorial) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
