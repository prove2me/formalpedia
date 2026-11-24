-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Main_unitAt_one
-- name    : Formalism.L2.Th1.E.Main.unitAt_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:52.954979+00:00
-- url     : https://prove2.me/theorems/52eadafd-9ba4-4bd5-b969-9a809a464065
-- title:
--   Main: unit At one
-- statement:
--   The Main construction uses the unit At one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXOffOrigin.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXOffOrigin.lean#L20-L20

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXOffOrigin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Main
variable {K : Type} [NormedField K]

theorem Formalism.L2.Th1.E.Main.unitAt_one : UnitAt 0 (1 : K⟦X⟧) := by sorry
