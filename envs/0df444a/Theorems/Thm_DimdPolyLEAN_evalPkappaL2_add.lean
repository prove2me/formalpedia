-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappaL2_add
-- name    : DimdPolyLEAN.evalPkappaL2_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:06.876592+00:00
-- url     : https://prove2.me/theorems/96ff0e1c-0421-4587-92a4-2f43ce3caa33
-- title:
--   Dimd Poly LEAN: eval Pkappa L2 add
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa L2 add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L642-L659
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L642-L659

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

theorem DimdPolyLEAN.evalPkappaL2_add
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    evalPkappaL2 kappa (F + G) = evalPkappaL2 kappa F + evalPkappaL2 kappa G := by sorry
