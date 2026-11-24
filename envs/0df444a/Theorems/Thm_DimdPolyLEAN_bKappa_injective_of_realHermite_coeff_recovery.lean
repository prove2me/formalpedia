-- Prove2me | Theorems.Thm_DimdPolyLEAN_bKappa_injective_of_realHermite_coeff_recovery
-- name    : DimdPolyLEAN.bKappa_injective_of_realHermite_coeff_recovery
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:24:35.331637+00:00
-- url     : https://prove2.me/theorems/aad1f496-0783-4e95-a304-cbb5da5b427e
-- title:
--   Dimd Poly LEAN: b Kappa injective of real Hermite coeff recovery
-- statement:
--   The Dimd Poly LEAN construction uses the b Kappa injective of real Hermite coeff recovery property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2858-L2866
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2858-L2866

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

theorem DimdPolyLEAN.bKappa_injective_of_realHermite_coeff_recovery
    {d : Nat} (kappa : MultiIndex d)
    (hcoeff : ∀ (U : Skappa d kappa) (alpha : Idx d),
      coeffSkappa U alpha =
        inner ℂ (realHermiteTensorL2 alpha) (bKappa kappa U)) :
    Function.Injective (bKappa kappa) := by sorry
