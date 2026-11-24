-- Prove2me | Theorems.Thm_DimdPolyLEAN_rankOneKernel_ae_to_unimodular_phase
-- name    : DimdPolyLEAN.rankOneKernel_ae_to_unimodular_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:25:01.782831+00:00
-- url     : https://prove2.me/theorems/6085e7b8-7447-4f7c-90e0-76256fbea786
-- title:
--   Dimd Poly LEAN: rank One Kernel ae to unimodular phase
-- statement:
--   The Dimd Poly LEAN construction uses the rank One Kernel ae to unimodular phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L5773-L5789
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L5773-L5789

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

theorem DimdPolyLEAN.rankOneKernel_ae_to_unimodular_phase
    {d : Nat} {f g : L2Real d} {fRep gRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep) (hg_rep : IsL2Rep g gRep)
    (hkernel :
      (fun p : RealVec d × RealVec d => fRep p.1 * star (fRep p.2))
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d × RealVec d))]
          fun p => gRep p.1 * star (gRep p.2)) :
    (f = 0 ∧ g = 0) ∨ ∃ w : ℂ, ‖w‖ = 1 ∧ g = w • f := by sorry
