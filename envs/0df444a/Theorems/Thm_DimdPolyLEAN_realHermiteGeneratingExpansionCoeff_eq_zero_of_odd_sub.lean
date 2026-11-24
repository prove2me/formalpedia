-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_sub
-- name    : DimdPolyLEAN.realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:22.756702+00:00
-- url     : https://prove2.me/theorems/c80f5ab9-f077-41c6-9695-ef2d766cc371
-- title:
--   Dimd Poly LEAN: real Hermite Generating Expansion Coeff eq zero of odd sub
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Generating Expansion Coeff eq zero of odd sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1398-L1402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1398-L1402

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

theorem DimdPolyLEAN.realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_sub
    {n k : ℕ} (hodd : Odd (n - k)) :
    realHermiteGeneratingExpansionCoeff n k = 0 := by sorry
