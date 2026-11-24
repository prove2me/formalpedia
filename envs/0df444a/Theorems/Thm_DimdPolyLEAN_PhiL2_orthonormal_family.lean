-- Prove2me | Theorems.Thm_DimdPolyLEAN_PhiL2_orthonormal_family
-- name    : DimdPolyLEAN.PhiL2_orthonormal_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:45.36121+00:00
-- url     : https://prove2.me/theorems/7a385260-c3e3-4df3-b024-3b63f6c70f0d
-- title:
--   Dimd Poly LEAN: Phi L2 orthonormal family
-- statement:
--   The Dimd Poly LEAN construction uses the Phi L2 orthonormal family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L734-L740
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L734-L740

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

theorem DimdPolyLEAN.PhiL2_orthonormal_family
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    Orthonormal ℂ (fun alpha : Idx d => PhiL2 kappa alpha) := by sorry
