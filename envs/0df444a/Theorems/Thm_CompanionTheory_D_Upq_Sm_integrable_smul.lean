-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_integrable_smul
-- name    : CompanionTheory.D.Upq.Sm.integrable_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:41:29.325818+00:00
-- url     : https://prove2.me/theorems/39e13582-de90-4df7-98cd-c30344328ef3
-- title:
--   Sm: integrable smul
-- statement:
--   The Sm construction uses the integrable smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L146-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L146-L152

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
variable {hG : IsMatGroup G}

theorem CompanionTheory.D.Upq.Sm.integrable_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : Mat n → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {f : MG G hG → V} (hf : Continuous f) :
    Integrable (fun g : MG G hG => φ g.mat • f g) haar := by sorry
