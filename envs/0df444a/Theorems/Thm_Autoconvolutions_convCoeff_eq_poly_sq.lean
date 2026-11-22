-- Prove2me | Theorems.Thm_Autoconvolutions_convCoeff_eq_poly_sq
-- name    : Autoconvolutions.convCoeff_eq_poly_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:30.818429+00:00
-- url     : https://prove2.me/theorems/58c5487e-b984-44d4-8082-661d06b6ec68
-- title:
--   Autoconvolutions: conv Coeff eq poly sq
-- statement:
--   The Autoconvolutions construction uses the conv Coeff eq poly sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/PolyStep.lean#L35-L37
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/PolyStep.lean#L35-L37

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

theorem Autoconvolutions.convCoeff_eq_poly_sq (F : Polynomial ℝ) (k : ℕ) :
    convCoeff F.natDegree (Polynomial.toFn (F.natDegree + 1) F) (k : ℤ) = (F^2).coeff k := by sorry
