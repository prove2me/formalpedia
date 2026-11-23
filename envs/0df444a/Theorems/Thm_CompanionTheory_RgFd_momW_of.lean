-- Prove2me | Theorems.Thm_CompanionTheory_RgFd_momW_of
-- name    : CompanionTheory.RgFd.momW_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:17.422187+00:00
-- url     : https://prove2.me/theorems/61fd2e7d-578b-4b51-aa0c-9c2e7984254b
-- title:
--   Rg Fd: mom W of
-- statement:
--   The Rg Fd construction uses the mom W of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/FormalDegrees/ArchimedeanFormalDegrees/MomentRecursion/MomStep.lean#L92-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/FormalDegrees/ArchimedeanFormalDegrees/MomentRecursion/MomStep.lean#L92-L103

import Definitions.Def_CompanionTheory_RealGroups_FormalDegrees_ArchimedeanFormalDegrees_MomB
import Definitions.Def_CompanionTheory_RealGroups_FormalDegrees_ArchimedeanFormalDegrees_MomentRecursion_MomStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open CompanionTheory CompanionTheory.RgFd

theorem CompanionTheory.RgFd.momW_of : MomA → MomB → MomW := by sorry
