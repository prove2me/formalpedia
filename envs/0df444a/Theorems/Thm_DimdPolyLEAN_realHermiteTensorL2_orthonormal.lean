-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteTensorL2_orthonormal
-- name    : DimdPolyLEAN.realHermiteTensorL2_orthonormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:34.616336+00:00
-- url     : https://prove2.me/theorems/36571bb9-0362-42d4-8c42-97631151d7f4
-- title:
--   Dimd Poly LEAN: real Hermite Tensor L2 orthonormal
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Tensor L2 orthonormal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2761-L2784
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2761-L2784

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

theorem DimdPolyLEAN.realHermiteTensorL2_orthonormal {d : Nat} :
    Orthonormal ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha) := by sorry
