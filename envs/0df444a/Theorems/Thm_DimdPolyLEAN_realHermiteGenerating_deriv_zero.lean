-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_deriv_zero
-- name    : DimdPolyLEAN.realHermiteGenerating_deriv_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:22:32.423796+00:00
-- url     : https://prove2.me/theorems/c77579f1-f634-426b-ba92-a154edbb90a1
-- title:
--   Dimd Poly LEAN: real Hermite Generating deriv zero
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Generating deriv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L862-L888
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L862-L888

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

theorem DimdPolyLEAN.realHermiteGenerating_deriv_zero (t : ℝ) :
    deriv (realHermiteGenerating t) 0 =
      (Real.sqrt 2 : ℂ) * (t : ℂ) * ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(((t : ℂ) ^ 2) / 2)) := by sorry
