-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_mem_lieJ
-- name    : CompanionTheory.D.Upq.mem_lieJ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:48.830946+00:00
-- url     : https://prove2.me/theorems/fa9598ed-dab7-4f4f-8d53-00ed244fb557
-- title:
--   Upq: mem lie J
-- statement:
--   The Upq construction uses the mem lie J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L30-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L30-L30

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (J : Matrix n n ℂ)

theorem CompanionTheory.D.Upq.mem_lieJ {X : Matrix n n ℂ} : X ∈ lieJ J ↔ Xᴴ * J + J * X = 0 := by sorry
