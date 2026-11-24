-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermite1D_inner_zero_zero
-- name    : DimdPolyLEAN.realHermite1D_inner_zero_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:38:58.689801+00:00
-- url     : https://prove2.me/theorems/2fa868d7-d8cf-4346-bb54-4e09fd177dfa
-- title:
--   Dimd Poly LEAN: real Hermite1 D inner zero zero
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite1 D inner zero zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2533-L2536
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2533-L2536

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

theorem DimdPolyLEAN.realHermite1D_inner_zero_zero :
    (∫ t : ℝ, realHermite1D 0 t * star (realHermite1D 0 t)) = 1 := by sorry
