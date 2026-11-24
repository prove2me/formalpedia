-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_integral_mem_of_isClosed
-- name    : CompanionTheory.D.Upq.Sm.integral_mem_of_isClosed
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:41:12.272374+00:00
-- url     : https://prove2.me/theorems/6d6d4de4-914e-4072-8c5e-f91a4a85ccc4
-- title:
--   Sm: integral mem of is Closed
-- statement:
--   The Sm construction uses the integral mem of is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L41-L48

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

theorem CompanionTheory.D.Upq.Sm.integral_mem_of_isClosed {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] {μ : Measure α} (S : Submodule ℂ V)
    (hS : IsClosed (S : Set V)) {f : α → V} (hf : ∀ a, f a ∈ S) : ∫ a, f a ∂μ ∈ S := by sorry
