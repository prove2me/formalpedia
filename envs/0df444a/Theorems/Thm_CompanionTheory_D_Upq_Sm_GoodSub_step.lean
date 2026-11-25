-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_GoodSub_step
-- name    : CompanionTheory.D.Upq.Sm.GoodSub.step
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:42:35.631543+00:00
-- url     : https://prove2.me/theorems/8cec2a49-bffb-50ac-bb25-06a3c1ea170f
-- title:
--   Good Sub: step
-- statement:
--   The Good Sub construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/UniformCoefficientBounds/CoefBoundUniform.lean#L67-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/UniformCoefficientBounds/CoefBoundUniform.lean#L67-L118

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

theorem CompanionTheory.D.Upq.Sm.GoodSub.step (hG : IsMatGroup G) (h : RepOn G σ) (hK : K ⊆ G) {T : Submodule ℂ H}
    (hT : GoodSub G K σ T) : ∃ (T' : Submodule ℂ H) (C : ℝ), GoodSub G K σ T' ∧ T ≤ T' ∧ 0 ≤ C ∧
      ∀ X, (∀ t, ex X t ∈ G) → ‖X‖ ≤ 1 → ∀ v ∈ T, ds σ X v ∈ T' ∧ ‖ds σ X v‖ ≤ C * ‖v‖ := by sorry
