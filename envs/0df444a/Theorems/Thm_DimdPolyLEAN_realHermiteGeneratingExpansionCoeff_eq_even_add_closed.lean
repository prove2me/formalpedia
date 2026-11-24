-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteGeneratingExpansionCoeff_eq_even_add_closed
-- name    : DimdPolyLEAN.realHermiteGeneratingExpansionCoeff_eq_even_add_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:36.524282+00:00
-- url     : https://prove2.me/theorems/b622dccb-bc3a-4783-a93f-5a0517f86d94
-- title:
--   Dimd Poly LEAN: real Hermite Generating Expansion Coeff eq even add closed
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Generating Expansion Coeff eq even add closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1421-L1430
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1421-L1430

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

theorem DimdPolyLEAN.realHermiteGeneratingExpansionCoeff_eq_even_add_closed
    {n k : ℕ} (hk : k ≤ n) (heven : Even (n + k)) :
    realHermiteGeneratingExpansionCoeff n k =
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
          ((-1 : ℂ) ^ ((n - k) / 2) *
            (((n - k) - 1)‼ : ℂ)))) := by sorry
