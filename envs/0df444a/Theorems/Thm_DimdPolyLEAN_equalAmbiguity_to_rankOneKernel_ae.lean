-- Prove2me | Theorems.Thm_DimdPolyLEAN_equalAmbiguity_to_rankOneKernel_ae
-- name    : DimdPolyLEAN.equalAmbiguity_to_rankOneKernel_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:25:05.26573+00:00
-- url     : https://prove2.me/theorems/fdd6bcb6-39e5-44d4-a9b7-632fef5854e4
-- title:
--   Dimd Poly LEAN: equal Ambiguity to rank One Kernel ae
-- statement:
--   The Dimd Poly LEAN construction uses the equal Ambiguity to rank One Kernel ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L5492-L5637
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L5492-L5637

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

theorem DimdPolyLEAN.equalAmbiguity_to_rankOneKernel_ae
    {d : Nat} {f g : L2Real d} {fRep gRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep) (hg_rep : IsL2Rep g gRep)
    (hAmb : ∀ ξ : PhaseSpace d, ambiguityRep f f ξ = ambiguityRep g g ξ) :
    (fun p : RealVec d × RealVec d => fRep p.1 * star (fRep p.2))
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d × RealVec d))]
        fun p => gRep p.1 * star (gRep p.2) := by sorry
