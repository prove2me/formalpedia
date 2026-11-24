-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteTensorL2_inner_eq_integral_of_memLp
-- name    : DimdPolyLEAN.realHermiteTensorL2_inner_eq_integral_of_memLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:10.076697+00:00
-- url     : https://prove2.me/theorems/b87f39e9-b4f3-4207-b6b5-5a16fe5e22e5
-- title:
--   Dimd Poly LEAN: real Hermite Tensor L2 inner eq integral of mem Lp
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Tensor L2 inner eq integral of mem Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2627-L2640
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2627-L2640

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

theorem DimdPolyLEAN.realHermiteTensorL2_inner_eq_integral_of_memLp
    {d : Nat} (alpha beta : Idx d)
    (hα : MemLp (realHermiteTensorRep alpha) 2
      (volume : Measure (RealVec d)))
    (hβ : MemLp (realHermiteTensorRep beta) 2
      (volume : Measure (RealVec d))) :
    inner ℂ (realHermiteTensorL2 alpha) (realHermiteTensorL2 beta) =
      ∫ x : RealVec d,
        realHermiteTensorRep beta x * star (realHermiteTensorRep alpha x) := by sorry
