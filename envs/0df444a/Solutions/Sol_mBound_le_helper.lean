-- Prove2me | solution 1 for mBound_le_helper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:46:54.437583+00:00
-- url     : https://prove2.me/submissions/00931fc8-67c8-4e3a-ba5c-7c89baa07fd1

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
import Theorems.Thm_ceil_nat_mul_le
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


attribute [local simp] mBound_zero
attribute [local simp] mBound_one
attribute [local simp] mBound_pos
attribute [local simp] mBound_ne_zero
section
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
open Real
private lemma mBound_pos_aux {k : ℕ} : 0 < 2 * log (log k) + 4.2 := by
  obtain rfl | rfl | hk : k = 0 ∨ k = 1 ∨ 2 ≤ k := by grind
  · norm_num
  · norm_num
  suffices -2 ≤ log (log k) by linear_combination 2 * this
  grw [le_log_iff_exp_le (log_pos (by simpa)), exp_neg, ← exp_one_rpow, ← hk, Nat.cast_ofNat,
    ← exp_one_gt_d9, ← log_two_gt_d9]
  norm_num
open Asymptotics Filter Topology
end

set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
open Real
theorem _root_.solution {k : ℕ} :
    mBound k ≤ k * (3 * log k + (2 * log (log k) + 6.2)) := by
  obtain rfl | rfl | hk : k = 0 ∨ k = 1 ∨ 2 ≤ k := by grind
  · simp
  · norm_num
  grw [mBound, ceil_nat_mul_le, Nat.cast_mul, Nat.ceil_lt_add_one _]
  · linear_combination
  apply add_nonneg
  · positivity
  linear_combination mBound_pos_aux
