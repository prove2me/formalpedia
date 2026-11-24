-- Prove2me | Theorems.Thm_DimdPolyLEAN_toFun_rotateCoord_circle_phase_tsum
-- name    : DimdPolyLEAN.toFun_rotateCoord_circle_phase_tsum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:34:15.408711+00:00
-- url     : https://prove2.me/theorems/f541f4ec-307f-4b2b-900a-6dcec6f834be
-- title:
--   Dimd Poly LEAN: to Fun rotate Coord circle phase tsum
-- statement:
--   The Dimd Poly LEAN construction uses the to Fun rotate Coord circle phase tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L449-L486
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L449-L486

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN

theorem DimdPolyLEAN.toFun_rotateCoord_circle_phase_tsum
    {d : Nat} (kappa : MultiIndex d) (q0 : Fin d)
    (U : Skappa d kappa) (x : Circle) (z : Cd d) :
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
      toFun kappa U
        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) =
      ∑' alpha : Idx d,
        coeffSkappa U alpha * Phi kappa alpha z * circleChar (alpha q0) x := by sorry
