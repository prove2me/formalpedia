-- Prove2me | Theorems.Thm_DimdPolyLEAN_skappa_ext_of_coeff_eq
-- name    : DimdPolyLEAN.skappa_ext_of_coeff_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:28.985587+00:00
-- url     : https://prove2.me/theorems/26816133-c2e9-444e-aa15-daa865bb6205
-- title:
--   Dimd Poly LEAN: skappa ext of coeff eq
-- statement:
--   The Dimd Poly LEAN construction uses the skappa ext of coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1348-L1357
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1348-L1357

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

theorem DimdPolyLEAN.skappa_ext_of_coeff_eq
    {d : Nat} {kappa : MultiIndex d} {U V : Skappa d kappa}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = coeffSkappa V alpha) :
    U = V := by sorry
