-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteTensorRep_memLp_of_realHermite1D_memLp
-- name    : DimdPolyLEAN.realHermiteTensorRep_memLp_of_realHermite1D_memLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:38.187097+00:00
-- url     : https://prove2.me/theorems/5c3316f6-7a4e-4b90-aaaf-f4e750800788
-- title:
--   Dimd Poly LEAN: real Hermite Tensor Rep mem Lp of real Hermite1 D mem Lp
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Tensor Rep mem Lp of real Hermite1 D mem Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2676-L2704
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2676-L2704

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

theorem DimdPolyLEAN.realHermiteTensorRep_memLp_of_realHermite1D_memLp
    {d : Nat} (alpha : Idx d)
    (hmem1 : ∀ n : Nat, MemLp (realHermite1D n) 2 (volume : Measure ℝ)) :
    MemLp (realHermiteTensorRep alpha) 2 (volume : Measure (RealVec d)) := by sorry
