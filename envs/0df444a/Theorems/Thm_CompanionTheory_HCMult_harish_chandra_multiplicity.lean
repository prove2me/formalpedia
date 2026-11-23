-- Prove2me | Theorems.Thm_CompanionTheory_HCMult_harish_chandra_multiplicity
-- name    : CompanionTheory.HCMult.harish_chandra_multiplicity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:24.274788+00:00
-- url     : https://prove2.me/theorems/46525ced-ff31-4b24-b245-8ed201447e26
-- title:
--   HCMult: harish chandra multiplicity
-- statement:
--   The HCMult construction uses the harish chandra multiplicity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HarishChandraMultiplicity/HCMult.lean#L12-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HarishChandraMultiplicity/HCMult.lean#L12-L52

import Definitions.Def_Formalism_PeriodIntegrals_HCMult
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinalAll
import Definitions.Def_CompanionTheory_AutomorphicTheory_HarishChandraMultiplicity_HCMult
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.HCMult
open PI.UpqRep CompanionTheory.D.gk.admitted

theorem CompanionTheory.HCMult.harish_chandra_multiplicity : PI.HCMult := by sorry
