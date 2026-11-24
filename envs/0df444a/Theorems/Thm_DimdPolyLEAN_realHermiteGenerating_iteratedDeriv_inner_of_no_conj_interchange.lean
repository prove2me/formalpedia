-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_inner_of_no_conj_interchange
-- name    : DimdPolyLEAN.realHermiteGenerating_iteratedDeriv_inner_of_no_conj_interchange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:16.585476+00:00
-- url     : https://prove2.me/theorems/c12b024e-3256-45ef-a616-0b1af1b746c5
-- title:
--   Dimd Poly LEAN: real Hermite Generating iterated Deriv inner of no conj interchange
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Generating iterated Deriv inner of no conj interchange property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2474-L2512
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2474-L2512

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

theorem DimdPolyLEAN.realHermiteGenerating_iteratedDeriv_inner_of_no_conj_interchange
    (n m : ℕ)
    (hinterchange :
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating t) 0 *
          iteratedDeriv m (realHermiteGenerating t) 0) =
        iteratedDeriv m
          (fun w : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        star (iteratedDeriv m (realHermiteGenerating t) 0)) =
      if n = m then (Nat.factorial n : ℂ) else 0 := by sorry
