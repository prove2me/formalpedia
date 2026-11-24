-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermite1D_memLp_inner_orthonormal
-- name    : DimdPolyLEAN.realHermite1D_memLp_inner_orthonormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:21.835155+00:00
-- url     : https://prove2.me/theorems/74fdcf39-b8cc-43cf-a8b8-aed8d9a03ada
-- title:
--   Dimd Poly LEAN: real Hermite1 D mem Lp inner orthonormal
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite1 D mem Lp inner orthonormal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2659-L2674
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L2659-L2674

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

theorem DimdPolyLEAN.realHermite1D_memLp_inner_orthonormal :
    (∀ n : Nat, MemLp (realHermite1D n) 2 (volume : Measure ℝ)) ∧
      ∀ n m : Nat,
        (∫ t : ℝ, realHermite1D m t * star (realHermite1D n t)) =
          if n = m then (1 : ℂ) else 0 := by sorry
