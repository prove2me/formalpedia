-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappa_truncateFinset
-- name    : DimdPolyLEAN.evalPkappa_truncateFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:55.184426+00:00
-- url     : https://prove2.me/theorems/4feebd6e-31c1-46b1-bfe8-192adb21d43e
-- title:
--   Dimd Poly LEAN: eval Pkappa truncate Finset
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa truncate Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L781-L806
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L781-L806

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

theorem DimdPolyLEAN.evalPkappa_truncateFinset
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    (E : Finset (Idx d)) :
    evalPkappa kappa (truncateFinset E U) =
      fun z : Cd d => ∑ alpha ∈ E, coeffSkappa U alpha * Phi kappa alpha z := by sorry
