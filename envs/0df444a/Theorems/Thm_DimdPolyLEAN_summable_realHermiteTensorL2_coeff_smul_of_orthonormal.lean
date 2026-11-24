-- Prove2me | Theorems.Thm_DimdPolyLEAN_summable_realHermiteTensorL2_coeff_smul_of_orthonormal
-- name    : DimdPolyLEAN.summable_realHermiteTensorL2_coeff_smul_of_orthonormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:39.102635+00:00
-- url     : https://prove2.me/theorems/bb50418b-5142-4939-a698-0bc43c1970d0
-- title:
--   Dimd Poly LEAN: summable real Hermite Tensor L2 coeff smul of orthonormal
-- statement:
--   The Dimd Poly LEAN construction uses the summable real Hermite Tensor L2 coeff smul of orthonormal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2806-L2816
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2806-L2816

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

theorem DimdPolyLEAN.summable_realHermiteTensorL2_coeff_smul_of_orthonormal
    {d : Nat} (kappa : MultiIndex d)
    (horth : Orthonormal ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha))
    (U : Skappa d kappa) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha • realHermiteTensorL2 alpha) := by sorry
