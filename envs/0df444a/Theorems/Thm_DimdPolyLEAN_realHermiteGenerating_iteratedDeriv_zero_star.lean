-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_zero_star
-- name    : DimdPolyLEAN.realHermiteGenerating_iteratedDeriv_zero_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:17:41.900488+00:00
-- url     : https://prove2.me/theorems/77b71e03-3cd4-48a6-9ae5-da7c0434da1c
-- title:
--   Dimd Poly LEAN: real Hermite Generating iterated Deriv zero star
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Generating iterated Deriv zero star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2082-L2091
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2082-L2091

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

theorem DimdPolyLEAN.realHermiteGenerating_iteratedDeriv_zero_star (n : ℕ) (t : ℝ) :
    star (iteratedDeriv n (realHermiteGenerating t) 0) =
      iteratedDeriv n (realHermiteGenerating t) 0 := by sorry
