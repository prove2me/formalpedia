-- Prove2me | Theorems.Thm_Autoconvolutions_poly_sum_eq_eval_one
-- name    : Autoconvolutions.poly_sum_eq_eval_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:38.391252+00:00
-- url     : https://prove2.me/theorems/bfb75aa7-c76f-4472-9335-424bc0f60aea
-- title:
--   Autoconvolutions: poly sum eq eval one
-- statement:
--   The Autoconvolutions construction uses the poly sum eq eval one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/PolyStep.lean#L47-L50
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/PolyStep.lean#L47-L50

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

theorem Autoconvolutions.poly_sum_eq_eval_one (F : Polynomial ℝ) :
    (∑ i : Fin (F.natDegree+1), Polynomial.toFn (F.natDegree+1) F i) = F.eval 1 := by sorry
