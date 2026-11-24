-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappaL2_truncateFinset
-- name    : DimdPolyLEAN.evalPkappaL2_truncateFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:46.959868+00:00
-- url     : https://prove2.me/theorems/91fe2d21-418d-4a86-8cae-c9c756b584af
-- title:
--   Dimd Poly LEAN: eval Pkappa L2 truncate Finset
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa L2 truncate Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L754-L768
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L754-L768

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

theorem DimdPolyLEAN.evalPkappaL2_truncateFinset
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    (E : Finset (Idx d)) :
    evalPkappaL2 kappa (truncateFinset E U) =
      ∑ alpha ∈ E, coeffSkappa U alpha • PhiL2 kappa alpha := by sorry
