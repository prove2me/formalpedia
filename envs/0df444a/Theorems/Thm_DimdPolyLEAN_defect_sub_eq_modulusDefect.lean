-- Prove2me | Theorems.Thm_DimdPolyLEAN_defect_sub_eq_modulusDefect
-- name    : DimdPolyLEAN.defect_sub_eq_modulusDefect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:18.521882+00:00
-- url     : https://prove2.me/theorems/781d5e97-9825-425a-a459-f9dc37b0f810
-- title:
--   Dimd Poly LEAN: defect sub eq modulus Defect
-- statement:
--   Rewriting the perturbation defect as the two-signal modulus defect.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/PhaseStability.lean#L416-L422
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/PhaseStability.lean#L416-L422

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
open DimdPolyLEAN

theorem DimdPolyLEAN.defect_sub_eq_modulusDefect
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F Q : Pkappa d kappa) :
    defect F (Q - F) = modulusDefect kappa F Q := by sorry
