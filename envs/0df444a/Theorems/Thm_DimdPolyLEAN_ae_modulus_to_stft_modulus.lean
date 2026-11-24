-- Prove2me | Theorems.Thm_DimdPolyLEAN_ae_modulus_to_stft_modulus
-- name    : DimdPolyLEAN.ae_modulus_to_stft_modulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:25:31.031268+00:00
-- url     : https://prove2.me/theorems/be328889-8f72-4b38-9394-b122452d3423
-- title:
--   Dimd Poly LEAN: ae modulus to stft modulus
-- statement:
--   The Dimd Poly LEAN construction uses the ae modulus to stft modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L5828-L5839
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L5828-L5839

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

theorem DimdPolyLEAN.ae_modulus_to_stft_modulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {U V : Skappa d kappa}
    (hmod :
      (fun z => ‖toFun kappa U z‖) =ᵐ[gammaD d]
        fun z => ‖toFun kappa V z‖) :
    ∀ ξ, ‖stftRep (varphiKappa kappa) (bKappa kappa U) ξ‖ =
      ‖stftRep (varphiKappa kappa) (bKappa kappa V) ξ‖ := by sorry
