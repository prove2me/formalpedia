-- Prove2me | Theorems.Thm_DimdPolyLEAN_projFinset_idempotent
-- name    : DimdPolyLEAN.projFinset_idempotent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:33:30.31305+00:00
-- url     : https://prove2.me/theorems/2c6388bf-b919-4c68-82fd-fe761c578851
-- title:
--   Dimd Poly LEAN: proj Finset idempotent
-- statement:
--   The Dimd Poly LEAN construction uses the proj Finset idempotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L82-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L82-L90

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

theorem DimdPolyLEAN.projFinset_idempotent
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (E : Finset (Idx d)) (F : Pkappa d kappa) :
    projFinset E (projFinset E F) = projFinset E F := by sorry
