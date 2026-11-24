-- Prove2me | Theorems.Thm_DimdPolyLEAN_Phi_rotateCoord_circle_phase
-- name    : DimdPolyLEAN.Phi_rotateCoord_circle_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:17:34.060094+00:00
-- url     : https://prove2.me/theorems/00e226c7-b2d2-45e6-967b-f4cac6f6e0fe
-- title:
--   Dimd Poly LEAN: Phi rotate Coord circle phase
-- statement:
--   The Dimd Poly LEAN construction uses the Phi rotate Coord circle phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L244-L273
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L244-L273

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

theorem DimdPolyLEAN.Phi_rotateCoord_circle_phase
    {d : Nat} (kappa alpha : MultiIndex d) (q0 : Fin d)
    (x : Circle) (z : Cd d) :
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
      Phi kappa alpha
        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) =
    (fourier ((alpha q0 : Nat) : Int) x : ℂ) *
      Phi kappa alpha z := by sorry
