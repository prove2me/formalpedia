-- Prove2me | solution 1 for linear_le_mBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:44:19.505972+00:00
-- url     : https://prove2.me/submissions/a032ce2a-a3b4-4006-8079-013e9ec7c17d

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
import Theorems.Thm_le_mBound
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


attribute [local simp] mBound_zero
attribute [local simp] mBound_one

set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
open Real
theorem _root_.solution {k : ℕ} : 2 * k ≤ mBound k := by
  obtain rfl | rfl | hk : k = 0 ∨ k = 1 ∨ 2 ≤ k := by grind
  · simp
  · simp
  rify
  grw [← le_mBound]
  have : 2 / 3 ≤ log k := by grw [← hk, Nat.cast_two, ← log_two_gt_d9]; norm_num
  linear_combination 3 * k * this
