-- Prove2me | Theorems.Thm_DimdPolyLEAN_varphiKappa_isL2Rep
-- name    : DimdPolyLEAN.varphiKappa_isL2Rep
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:24:30.225546+00:00
-- url     : https://prove2.me/theorems/f57a0246-17a9-46c1-a134-b93b22387192
-- title:
--   Dimd Poly LEAN: varphi Kappa is L2 Rep
-- statement:
--   The Dimd Poly LEAN construction uses the varphi Kappa is L2 Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2786-L2796
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2786-L2796

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

theorem DimdPolyLEAN.varphiKappa_isL2Rep
    {d : Nat} (kappa : MultiIndex d) :
    IsL2Rep (varphiKappa kappa) (realHermiteTensorRep kappa) := by sorry
