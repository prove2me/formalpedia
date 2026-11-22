-- Prove2me | solution 1 for mBound_le_weak
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:48:51.614559+00:00
-- url     : https://prove2.me/submissions/a435a3c0-c1fa-4570-967c-fde08416f145

import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNRat.Floor
import Mathlib.Tactic.Rify
import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_Compactness
import Definitions.Def_Polychromatic_LocalLemma
import Definitions.Def_Polychromatic_Existence
import Theorems.Thm_mBound_zero
import Theorems.Thm_mBound_one
import Theorems.Thm_mBound_pos
import Theorems.Thm_mBound_ne_zero
import Theorems.Thm_mBound_le_helper
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


attribute [local simp] mBound_zero
attribute [local simp] mBound_one
attribute [local simp] mBound_pos
attribute [local simp] mBound_ne_zero

set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
open Real
theorem _root_.solution {k : ℕ} (hk : 4 ≤ k) : mBound k ≤ 8 * k * log k := by
  suffices 2 * log (log k) + 6.2 ≤ 5 * log k by
    linear_combination mBound_le_helper (k := k) + (k : ℝ) * this
  suffices ∀ x, 1.37 < x → 2 * log x + 6.2 ≤ 5 * x by
    apply this (log k)
    have : 1.37 < (2 : ℕ) * log 2 := by linear_combination 2 * log_two_gt_d9
    refine this.trans_le ?_
    grw [← hk, ← log_pow]
    norm_num
  intro x hx
  suffices StrictMonoOn (fun x ↦ x * 5 - 2 * log x) (Set.Ici 1.37) by
    have h₁ : log 1.37 ≤ 13 / 40 := by
      rw [log_le_iff_le_exp (by norm_num)]
      grw [← quadratic_le_exp_of_nonneg (by norm_num)]
      norm_num
    have h₂ := this (by simp) (by simp [hx.le]) hx
    linear_combination 2 * h₁ + h₂
  apply strictMonoOn_of_hasDerivWithinAt_pos (f' := fun x ↦ 5 - 2 * x⁻¹) (convex_Ici _)
  · apply ContinuousOn.sub (by fun_prop) (ContinuousOn.mul (by fun_prop) _)
    apply ContinuousOn.log (by fun_prop)
    simp only [Set.mem_Ici, ne_eq]
    intro x hx
    positivity
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x hx
    apply HasDerivWithinAt.sub
    · apply (hasDerivAt_mul_const _).hasDerivWithinAt
    apply HasDerivWithinAt.const_mul
    apply (hasDerivAt_log (by positivity)).hasDerivWithinAt
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi, sub_pos]
    intro y hy
    grw [← hy]
    norm_num
