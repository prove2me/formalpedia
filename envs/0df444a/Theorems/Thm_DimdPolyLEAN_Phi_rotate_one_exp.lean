-- Prove2me | Theorems.Thm_DimdPolyLEAN_Phi_rotate_one_exp
-- name    : DimdPolyLEAN.Phi_rotate_one_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:24.68794+00:00
-- url     : https://prove2.me/theorems/c702d9e4-115d-4142-9cbc-4145afafc95b
-- title:
--   Dimd Poly LEAN: Phi rotate one exp
-- statement:
--   The Dimd Poly LEAN construction uses the Phi rotate one exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L209-L233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L209-L233

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

theorem DimdPolyLEAN.Phi_rotate_one_exp
    {d : Nat} (kappa alpha : MultiIndex d) (q0 : Fin d) (t : ℝ) (z : Cd d) :
    Phi kappa alpha (Function.update z q0 (Complex.exp (Complex.I * t) * z q0)) =
      Complex.exp (Complex.I * (((alpha q0 : ℤ) - (kappa q0 : ℤ) : ℂ) * t)) *
        Phi kappa alpha z := by sorry
