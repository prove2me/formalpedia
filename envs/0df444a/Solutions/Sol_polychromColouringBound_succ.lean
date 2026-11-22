-- Prove2me | solution 1 for polychromColouringBound_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:04.29111+00:00
-- url     : https://prove2.me/submissions/1030fc1c-ccf4-4f5e-8026-f725b1ca61d9

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
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
open Real
theorem _root_.solution {k m : ℕ} (hk : k ≠ 0) (h : 2 * k ≤ m + 1)
    (hkm : polychromColouringBound k m) :
    polychromColouringBound k (m + 1) := by
  have : 0 ≤ 1 - (k : ℝ)⁻¹ := by
    simp only [sub_nonneg]
    apply inv_le_one_of_one_le₀ (by simp; lia)
  rw [polychromColouringBound, mul_right_comm _ _ (k : ℝ), mul_assoc (_ * _)] at hkm ⊢
  refine hkm.trans' ?_
  rw [pow_succ', ← mul_assoc (_ + 1 : ℝ), Nat.cast_add_one]
  gcongr _ * (?_ * _)
  simp only [add_sub_cancel_right, fieldLe]
  rify at h
  linear_combination (m : ℝ) * h
