-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_thetaG_smul
-- name    : CompanionTheory.D.Upq.thetaG_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:00.952619+00:00
-- url     : https://prove2.me/theorems/7193caac-1bd4-48c0-9a52-3f47eb8bd650
-- title:
--   Upq: theta G smul
-- statement:
--   The Upq construction uses the theta G smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L212-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L212-L213

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

theorem CompanionTheory.D.Upq.thetaG_smul (c : ℂ) (M : Matrix n n ℂ) : thetaG J (c • M) = star c • thetaG J M := by sorry
