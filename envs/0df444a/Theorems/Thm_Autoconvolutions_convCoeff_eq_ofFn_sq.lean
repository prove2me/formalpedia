-- Prove2me | Theorems.Thm_Autoconvolutions_convCoeff_eq_ofFn_sq
-- name    : Autoconvolutions.convCoeff_eq_ofFn_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:35.004803+00:00
-- url     : https://prove2.me/theorems/c1e9add6-484d-4eeb-8442-19b1a78ffc76
-- title:
--   Autoconvolutions: conv Coeff eq of Fn sq
-- statement:
--   The Autoconvolutions construction uses the conv Coeff eq of Fn sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/PolyStep.lean#L22-L33
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/PolyStep.lean#L22-L33

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

theorem Autoconvolutions.convCoeff_eq_ofFn_sq (d : ℕ) (p : Fin (d+1) → ℝ) (k : ℕ) :
    convCoeff d p (k : ℤ) = (Polynomial.ofFn (d+1) p ^ 2).coeff k := by sorry
