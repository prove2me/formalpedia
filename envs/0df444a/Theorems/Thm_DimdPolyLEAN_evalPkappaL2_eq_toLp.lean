-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappaL2_eq_toLp
-- name    : DimdPolyLEAN.evalPkappaL2_eq_toLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:03.894444+00:00
-- url     : https://prove2.me/theorems/f6c0d0d2-f8aa-45b9-91d9-428b8e97a14d
-- title:
--   Dimd Poly LEAN: eval Pkappa L2 eq to Lp
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa L2 eq to Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L634-L640
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L634-L640

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

theorem DimdPolyLEAN.evalPkappaL2_eq_toLp
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    evalPkappaL2 kappa F =
      (memLp_two_evalPkappa hd kappa F).toLp (evalPkappa kappa F) := by sorry
