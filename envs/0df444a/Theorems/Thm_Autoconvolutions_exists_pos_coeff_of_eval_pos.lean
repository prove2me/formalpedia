-- Prove2me | Theorems.Thm_Autoconvolutions_exists_pos_coeff_of_eval_pos
-- name    : Autoconvolutions.exists_pos_coeff_of_eval_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:37.440129+00:00
-- url     : https://prove2.me/theorems/7131e6cc-61bd-4959-8695-9e6936071e46
-- title:
--   Autoconvolutions: exists pos coeff of eval pos
-- statement:
--   The Autoconvolutions construction uses the exists pos coeff of eval pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/PolyStep.lean#L52-L56
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/PolyStep.lean#L52-L56

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

theorem Autoconvolutions.exists_pos_coeff_of_eval_pos (F : Polynomial ℝ) (hF : 0 < F.eval 1) :
    ∃ i : Fin (F.natDegree+1), 0 < Polynomial.toFn (F.natDegree+1) F i := by sorry
