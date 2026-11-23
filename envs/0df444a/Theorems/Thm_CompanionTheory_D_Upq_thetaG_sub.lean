-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_thetaG_sub
-- name    : CompanionTheory.D.Upq.thetaG_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:10.355836+00:00
-- url     : https://prove2.me/theorems/7d9488dc-75ef-4877-9fd6-daf99c2cd341
-- title:
--   Upq: theta G sub
-- statement:
--   The Upq construction uses the theta G sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L209-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L209-L210

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

theorem CompanionTheory.D.Upq.thetaG_sub (M N : Matrix n n ℂ) : thetaG J (M - N) = thetaG J M - thetaG J N := by sorry
