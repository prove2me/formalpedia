-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermite1D_inner_of_iteratedDeriv_inner
-- name    : DimdPolyLEAN.realHermite1D_inner_of_iteratedDeriv_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:04.497055+00:00
-- url     : https://prove2.me/theorems/04d9edab-c93d-4d9e-9f04-d1014badd849
-- title:
--   Dimd Poly LEAN: real Hermite1 D inner of iterated Deriv inner
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite1 D inner of iterated Deriv inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2007-L2050
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2007-L2050

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

theorem DimdPolyLEAN.realHermite1D_inner_of_iteratedDeriv_inner (n m : ℕ)
    (hderiv :
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating t) 0 *
          star (iteratedDeriv m (realHermiteGenerating t) 0)) =
        if n = m then (Nat.factorial n : ℂ) else 0) :
    (∫ t : ℝ, realHermite1D n t * star (realHermite1D m t)) =
      if n = m then 1 else 0 := by sorry
