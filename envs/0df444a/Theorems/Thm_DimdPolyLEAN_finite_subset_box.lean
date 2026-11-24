-- Prove2me | Theorems.Thm_DimdPolyLEAN_finite_subset_box
-- name    : DimdPolyLEAN.finite_subset_box
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:33.539816+00:00
-- url     : https://prove2.me/theorems/6e9cd709-6976-4a09-b767-7e39390a7252
-- title:
--   Dimd Poly LEAN: finite subset box
-- statement:
--   The Dimd Poly LEAN construction uses the finite subset box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L498-L506
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L498-L506

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

theorem DimdPolyLEAN.finite_subset_box
    {d : Nat} (E : Finset (Idx d)) :
    ∃ J : MultiIndex d, E ⊆ box J := by sorry
