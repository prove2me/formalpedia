-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_ex_neg_mul
-- name    : CompanionTheory.D.Upq.Sm.hasDerivAt_ex_neg_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:41:57.340543+00:00
-- url     : https://prove2.me/theorems/a672aef0-85d6-4e54-8bfe-c1b854efa13d
-- title:
--   Sm: has Deriv At ex neg mul
-- statement:
--   The Sm construction uses the has Deriv At ex neg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L76-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L76-L88

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

theorem CompanionTheory.D.Upq.Sm.hasDerivAt_ex_neg_mul (X g : Mat n) (t : ℝ) :
    HasDerivAt (fun s => ex X (-s) * g) (-(X * (ex X (-t) * g))) t := by sorry
