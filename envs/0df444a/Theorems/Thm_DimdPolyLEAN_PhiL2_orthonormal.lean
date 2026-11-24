-- Prove2me | Theorems.Thm_DimdPolyLEAN_PhiL2_orthonormal
-- name    : DimdPolyLEAN.PhiL2_orthonormal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:18:13.089182+00:00
-- url     : https://prove2.me/theorems/56bb1589-60bf-4fd4-8d26-114cf176f18d
-- title:
--   Dimd Poly LEAN: Phi L2 orthonormal
-- statement:
--   The Dimd Poly LEAN construction uses the Phi L2 orthonormal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L682-L703
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L682-L703

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

theorem DimdPolyLEAN.PhiL2_orthonormal
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (alpha beta : Idx d) :
    inner ℂ (PhiL2 kappa alpha) (PhiL2 kappa beta) =
      if alpha = beta then (1 : ℂ) else 0 := by sorry
