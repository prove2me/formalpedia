-- Prove2me | Theorems.Thm_Autoconvolutions_convCoeff_of_neg
-- name    : Autoconvolutions.convCoeff_of_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:30.664585+00:00
-- url     : https://prove2.me/theorems/6b155a0c-2229-4b6c-9318-74d2ecb9daf8
-- title:
--   Autoconvolutions: conv Coeff of neg
-- statement:
--   The Autoconvolutions construction uses the conv Coeff of neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/PolyStep.lean#L39-L45
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/PolyStep.lean#L39-L45

module
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Definitions.Def_Autoconvolutions_PolyStep
set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
noncomputable section
open Autoconvolutions

theorem Autoconvolutions.convCoeff_of_neg (d : ℕ) (p : Fin (d+1) → ℝ) {k : ℤ} (hk : k < 0) :
    convCoeff d p k = 0 := by sorry
