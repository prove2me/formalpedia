-- Prove2me | Theorems.Thm_DimdPolyLEAN_spectrogram_eq_of_equal_modulus_to_ambiguity_eq
-- name    : DimdPolyLEAN.spectrogram_eq_of_equal_modulus_to_ambiguity_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:25:04.514489+00:00
-- url     : https://prove2.me/theorems/71d87df4-0eae-4a55-b62b-b1539625769c
-- title:
--   Dimd Poly LEAN: spectrogram eq of equal modulus to ambiguity eq
-- statement:
--   The Dimd Poly LEAN construction uses the spectrogram eq of equal modulus to ambiguity eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L5122-L5154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L5122-L5154

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

theorem DimdPolyLEAN.spectrogram_eq_of_equal_modulus_to_ambiguity_eq
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {f g : L2Real d}
    (hmod : ∀ ξ : PhaseSpace d,
      ‖stftRep (varphiKappa kappa) f ξ‖ =
        ‖stftRep (varphiKappa kappa) g ξ‖) :
    ∀ ξ : PhaseSpace d, ambiguityRep f f ξ = ambiguityRep g g ξ := by sorry
