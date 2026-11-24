-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_Lx
-- name    : CompanionTheory.D.Upq.Sm.hasDerivAt_Lx
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:42:33.873746+00:00
-- url     : https://prove2.me/theorems/72b4231e-7b6f-4db1-81a5-449b97a069a1
-- title:
--   Sm: has Deriv At Lx
-- statement:
--   The Sm construction uses the has Deriv At Lx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L114-L118

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

theorem CompanionTheory.D.Upq.Sm.hasDerivAt_Lx (X g : Mat n) {φ : Mat n → ℝ} (hφ : ContDiff ℝ ∞ φ) (t : ℝ) :
    HasDerivAt (fun s => φ (ex X (-s) * g)) (Lx X φ (ex X (-t) * g)) t := by sorry
