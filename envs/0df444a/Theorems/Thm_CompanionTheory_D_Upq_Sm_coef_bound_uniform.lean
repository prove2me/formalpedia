-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_coef_bound_uniform
-- name    : CompanionTheory.D.Upq.Sm.coef_bound_uniform
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:13:40.261072+00:00
-- url     : https://prove2.me/theorems/ee45fe6d-b3b0-41e6-8a4a-e811e4170866
-- title:
--   Sm: coef bound uniform
-- statement:
--   The Sm construction uses the coef bound uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/UniformCoefficientBounds/CoefBoundUniform.lean#L144-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/UniformCoefficientBounds/CoefBoundUniform.lean#L144-L174

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G K : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem CompanionTheory.D.Upq.Sm.coef_bound_uniform {T : Submodule ℂ H} [FiniteDimensional ℂ T] {ρ : Mat n → ℝ}
    (hρ : ∀ g ∈ G, 0 ≤ ρ g)
    (hb : ∀ a ∈ T, ∀ b ∈ T, ∃ C : ℝ, ∀ g ∈ G, ‖⟪a, σ g b⟫_ℂ‖ ≤ C * ρ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ T, ∀ b ∈ T, ∀ g ∈ G, ‖⟪a, σ g b⟫_ℂ‖ ≤ C * ‖a‖ * ‖b‖ * ρ g := by sorry
