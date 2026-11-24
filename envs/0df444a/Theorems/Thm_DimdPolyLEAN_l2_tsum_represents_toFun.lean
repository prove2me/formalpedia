-- Prove2me | Theorems.Thm_DimdPolyLEAN_l2_tsum_represents_toFun
-- name    : DimdPolyLEAN.l2_tsum_represents_toFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:58.352428+00:00
-- url     : https://prove2.me/theorems/70266336-1706-48d2-a023-082ad0e990e7
-- title:
--   Dimd Poly LEAN: l2 tsum represents to Fun
-- statement:
--   The Dimd Poly LEAN construction uses the l2 tsum represents to Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1183-L1229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1183-L1229

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

theorem DimdPolyLEAN.l2_tsum_represents_toFun
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    IsTensorL2Rep
      (∑' alpha : Idx d, coeffSkappa U alpha • PhiL2 kappa alpha)
      (toFun kappa U) := by sorry
