-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_thetaG_add
-- name    : CompanionTheory.D.Upq.thetaG_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:33.173909+00:00
-- url     : https://prove2.me/theorems/e4907936-2fdc-4070-a638-135ce574b7dc
-- title:
--   Upq: theta G add
-- statement:
--   The Upq construction uses the theta G add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L206-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L206-L207

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
variable {J}

theorem CompanionTheory.D.Upq.thetaG_add (M N : Matrix n n ℂ) : thetaG J (M + N) = thetaG J M + thetaG J N := by sorry
