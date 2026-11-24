-- Prove2me | Theorems.Thm_DimdPolyLEAN_stft_model_modulus
-- name    : DimdPolyLEAN.stft_model_modulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:25:04.657123+00:00
-- url     : https://prove2.me/theorems/ca57558f-eaec-4850-8bff-61850db5c9f6
-- title:
--   Dimd Poly LEAN: stft model modulus
-- statement:
--   The Dimd Poly LEAN construction uses the stft model modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L4762-L4771
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L4762-L4771

module
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology

theorem DimdPolyLEAN.stft_model_modulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (U : Skappa d kappa) (ξ : PhaseSpace d) :
    ‖stftRep (varphiKappa kappa) (bKappa kappa U) ξ‖ =
      WKappa ξ * ‖toFun kappa U (TKappa ξ)‖ := by sorry
