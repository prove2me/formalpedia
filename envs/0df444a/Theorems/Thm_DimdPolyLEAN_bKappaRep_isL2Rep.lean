-- Prove2me | Theorems.Thm_DimdPolyLEAN_bKappaRep_isL2Rep
-- name    : DimdPolyLEAN.bKappaRep_isL2Rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:37.903356+00:00
-- url     : https://prove2.me/theorems/e86e609d-738f-45c2-9a3a-f7886524310b
-- title:
--   Dimd Poly LEAN: b Kappa Rep is L2 Rep
-- statement:
--   The Dimd Poly LEAN construction uses the b Kappa Rep is L2 Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2880-L2885
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2880-L2885

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

theorem DimdPolyLEAN.bKappaRep_isL2Rep
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) :
    IsL2Rep (bKappa kappa U) (bKappaRep kappa U) := by sorry
