-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_unit_at_rules
-- name    : Formalism.L2.Th1.E.unit_at_rules
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:12.96692+00:00
-- url     : https://prove2.me/theorems/7acdc352-44a6-4c15-8bbc-bd5ec9d2bf9c
-- title:
--   E: unit at rules
-- statement:
--   The E construction uses the unit at rules property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L257-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L257-L261

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E

theorem Formalism.L2.Th1.E.unit_at_rules : UnitAtRules := by sorry
