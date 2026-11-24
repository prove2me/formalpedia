-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappa_rotateCoord_circle_phase_sum
-- name    : DimdPolyLEAN.evalPkappa_rotateCoord_circle_phase_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:21.352823+00:00
-- url     : https://prove2.me/theorems/ec9cf6fd-b7a9-47d0-93c2-ce8a49d0e8f8
-- title:
--   Dimd Poly LEAN: eval Pkappa rotate Coord circle phase sum
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa rotate Coord circle phase sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L275-L305
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L275-L305

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

theorem DimdPolyLEAN.evalPkappa_rotateCoord_circle_phase_sum
    {d : Nat} (kappa : MultiIndex d) (q0 : Fin d)
    (F : Pkappa d kappa) (x : Circle) (z : Cd d) :
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
      evalPkappa kappa F
        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) =
      ∑ alpha ∈ F.support,
        F alpha * Phi kappa alpha z * circleChar (alpha q0) x := by sorry
