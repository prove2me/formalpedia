-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermite1D_memLp_inner_orthonormal_of_no_conj_interchange
-- name    : DimdPolyLEAN.realHermite1D_memLp_inner_orthonormal_of_no_conj_interchange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:04.527803+00:00
-- url     : https://prove2.me/theorems/5bead579-c11a-4e69-acce-2740688c7e04
-- title:
--   Dimd Poly LEAN: real Hermite1 D mem Lp inner orthonormal of no conj interchange
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite1 D mem Lp inner orthonormal of no conj interchange property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2553-L2568
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2553-L2568

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

theorem DimdPolyLEAN.realHermite1D_memLp_inner_orthonormal_of_no_conj_interchange
    (hmem : ∀ n : Nat, MemLp (realHermite1D n) 2 (volume : Measure ℝ))
    (hinterchange : ∀ n m : ℕ,
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating t) 0 *
          iteratedDeriv m (realHermiteGenerating t) 0) =
        iteratedDeriv m
          (fun w : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0) :
    (∀ n : Nat, MemLp (realHermite1D n) 2 (volume : Measure ℝ)) ∧
      ∀ n m : Nat,
        (∫ t : ℝ, realHermite1D m t * star (realHermite1D n t)) =
          if n = m then (1 : ℂ) else 0 := by sorry
