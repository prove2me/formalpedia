-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Main_unitAt_of_oneUnit
-- name    : Formalism.L2.Th1.E.Main.unitAt_of_oneUnit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:04.473415+00:00
-- url     : https://prove2.me/theorems/ba328140-2f13-4136-a14a-977e5df82e25
-- title:
--   Main: unit At of one Unit
-- statement:
--   The Main construction uses the unit At of one Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXOffOrigin.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXOffOrigin.lean#L25-L26

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

theorem Formalism.L2.Th1.E.Main.unitAt_of_oneUnit {a : K} {V : K⟦X⟧} (ha : ‖a‖ = 1) (hV : OneUnit V) : UnitAt 0 (C a * V) := by sorry
