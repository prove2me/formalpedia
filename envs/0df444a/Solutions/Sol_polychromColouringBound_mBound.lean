-- Prove2me | solution 1 for polychromColouringBound_mBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:49:38.689176+00:00
-- url     : https://prove2.me/submissions/f14b8404-9151-4043-b7dd-6e597fce8098

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
import Theorems.Thm_condition_of_mul_exp_le
import Theorems.Thm_mBound_zero
import Theorems.Thm_mBound_one
import Theorems.Thm_mBound_pos
import Theorems.Thm_mBound_ne_zero
import Theorems.Thm_mBound_le_weak
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
open Asymptotics Filter Topology
theorem _root_.solution {k : ℕ} (hk : 4 ≤ k) :
    polychromColouringBound k (mBound k) := by
  have hk' : k ≠ 0 := by grind
  have hk'' : 0 < log k := log_pos (by simp; lia)
  apply condition_of_mul_exp_le hk' (mBound_ne_zero hk')
  calc
    mBound k ^ 2 * k * exp (- mBound k / k + 1) ≤
        (8 * k * log k) ^ 2 * k * exp (- mBound k / k + 1) := by
      gcongr
      exact mBound_le_weak hk
    _ ≤ (8 * k * log k) ^ 2 * k * exp (- (3 * log k + (2 * log (log k) + 5.2)) + 1) := by
      grw [mBound, ← Nat.le_ceil, neg_div, mul_div_cancel_left₀ _ (by positivity)]
    _ = 2 ^ 6 * k ^ 3 * log k ^ 2 * exp (log k * (-3) + log (log k) * (-2) + - 4.2) := by ring_nf
    _ = 2 ^ 6 * exp (-4.2) := by
      rw [exp_add, exp_add, ← rpow_def_of_pos (by positivity),
        ← rpow_def_of_pos (by positivity)]
      simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg, zpow_ofNat]
      simp [field]
    _ ≤ 1 := by
      grw [← log_le_log_iff (by positivity) (by positivity),
        log_mul (by positivity) (by positivity), log_exp, log_one, log_pow, log_two_lt_d9]
      norm_num
