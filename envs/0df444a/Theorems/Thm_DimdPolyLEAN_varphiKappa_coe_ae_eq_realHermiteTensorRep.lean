-- Prove2me | Theorems.Thm_DimdPolyLEAN_varphiKappa_coe_ae_eq_realHermiteTensorRep
-- name    : DimdPolyLEAN.varphiKappa_coe_ae_eq_realHermiteTensorRep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:28.859284+00:00
-- url     : https://prove2.me/theorems/6e3f64f5-e3d4-4ba6-a17c-e86c2e24eaa5
-- title:
--   Dimd Poly LEAN: varphi Kappa coe ae eq real Hermite Tensor Rep
-- statement:
--   The Dimd Poly LEAN construction uses the varphi Kappa coe ae eq real Hermite Tensor Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2798-L2804
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2798-L2804

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

theorem DimdPolyLEAN.varphiKappa_coe_ae_eq_realHermiteTensorRep
    {d : Nat} (kappa : MultiIndex d) :
    ((varphiKappa kappa : L2Real d) : RealVec d -> ℂ)
      =ᵐ[(volume : Measure (RealVec d))] realHermiteTensorRep kappa := by sorry
