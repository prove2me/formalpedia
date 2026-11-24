-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteTensorL2_orthonormal_of_memLp_integral
-- name    : DimdPolyLEAN.realHermiteTensorL2_orthonormal_of_memLp_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:11.997841+00:00
-- url     : https://prove2.me/theorems/093295d7-f9ee-46ca-bd3c-6aea3f46d38d
-- title:
--   Dimd Poly LEAN: real Hermite Tensor L2 orthonormal of mem Lp integral
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Tensor L2 orthonormal of mem Lp integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2642-L2657
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2642-L2657

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

theorem DimdPolyLEAN.realHermiteTensorL2_orthonormal_of_memLp_integral
    {d : Nat}
    (hmem : ∀ alpha : Idx d,
      MemLp (realHermiteTensorRep alpha) 2
        (volume : Measure (RealVec d)))
    (hinner : ∀ alpha beta : Idx d,
      (∫ x : RealVec d,
        realHermiteTensorRep beta x * star (realHermiteTensorRep alpha x)) =
        if alpha = beta then (1 : ℂ) else 0) :
    Orthonormal ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha) := by sorry
