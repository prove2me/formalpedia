-- Prove2me | Theorems.Thm_DimdPolyLEAN_windowAmbiguity_dense_nonvanishing
-- name    : DimdPolyLEAN.windowAmbiguity_dense_nonvanishing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:25:00.077381+00:00
-- url     : https://prove2.me/theorems/7b7073f4-7d53-4ef6-8a48-fd6e9f5f1455
-- title:
--   Dimd Poly LEAN: window Ambiguity dense nonvanishing
-- statement:
--   The Dimd Poly LEAN construction uses the window Ambiguity dense nonvanishing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L5110-L5120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L5110-L5120

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

theorem DimdPolyLEAN.windowAmbiguity_dense_nonvanishing
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    Dense {ξ : PhaseSpace d |
      ambiguityRep (varphiKappa kappa) (varphiKappa kappa) ξ ≠ 0} := by sorry
