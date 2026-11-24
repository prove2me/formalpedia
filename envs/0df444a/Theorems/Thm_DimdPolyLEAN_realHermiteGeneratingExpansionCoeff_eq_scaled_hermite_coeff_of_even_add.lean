-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff_of_even_add
-- name    : DimdPolyLEAN.realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff_of_even_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:31.347485+00:00
-- url     : https://prove2.me/theorems/48723c9b-35c0-4eee-9932-2e5d1c71ae35
-- title:
--   Dimd Poly LEAN: real Hermite Generating Expansion Coeff eq scaled hermite coeff of even add
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Generating Expansion Coeff eq scaled hermite coeff of even add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1432-L1442
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1432-L1442

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

theorem DimdPolyLEAN.realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff_of_even_add
    {n k : ℕ} (hk : k ≤ n) (heven : Even (n + k)) :
    realHermiteGeneratingExpansionCoeff n k =
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((Real.sqrt 2 : ℂ) ^ k * ((Polynomial.hermite n).coeff k : ℂ))) := by sorry
