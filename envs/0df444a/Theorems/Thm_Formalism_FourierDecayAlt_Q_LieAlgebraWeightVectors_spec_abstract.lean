-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_spec_abstract
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.spec_abstract
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:45:56.731389+00:00
-- url     : https://prove2.me/theorems/85d599f0-5506-46f6-ac68-6868c07874d7
-- title:
--   Lie Algebra Weight Vectors: spec abstract
-- statement:
--   The Lie Algebra Weight Vectors construction uses the spec abstract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SpecAbstract.lean#L66-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SpecAbstract.lean#L66-L147

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SpecAbstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.spec_abstract {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] {X ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝓕 : Set (X → (Wq →L[ℂ] Wp))) (G : Set X)
    (h0 : (fun _ => (0 : Wq →L[ℂ] Wp)) ∈ 𝓕)
    (hadd : ∀ F₁ ∈ 𝓕, ∀ F₂ ∈ 𝓕, (fun x => F₁ x + F₂ x) ∈ 𝓕)
    (hsmul : ∀ F ∈ 𝓕, ∀ c : ℂ, (fun x => c • F x) ∈ 𝓕)
    (T : ℂ → (X → (Wq →L[ℂ] Wp)) → X → (Wq →L[ℂ] Wp)) (c : X → ℂ) (hc : ∀ g ∈ G, c g ≠ 0)
    (Y₀ : ℂ) (hA : ∀ F ∈ 𝓕, (fun x => (c x)⁻¹ • T Y₀ F x) ∈ 𝓕)
    (lam : ι → ℂ → ℂ) (hinj : Function.Injective (fun σ => lam σ Y₀))
    (S : X → ι → Submodule ℂ Wq) (hS : ∀ g ∈ G, DirectSum.IsInternal (S g))
    (heig : ∀ F ∈ 𝓕, ∀ g ∈ G, ∀ σ, ∀ v ∈ S g σ, ∀ Y, T Y F g v = (c g * lam σ Y) • F g v)
    (J : X → (Wq →L[ℂ] Wp)) (hJ : J ∈ 𝓕) :
    ∃ dec : ι → X → (Wq →L[ℂ] Wp), (∀ σ, dec σ ∈ 𝓕) ∧ (∀ g ∈ G, J g = ∑ σ, dec σ g) ∧
      (∀ σ Y, ∀ g ∈ G, T Y (dec σ) g = (c g * lam σ Y) • dec σ g) ∧
      ∀ g ∈ G, ∀ σ v, ∃ w ∈ S g σ, dec σ g v = J g w := by sorry
