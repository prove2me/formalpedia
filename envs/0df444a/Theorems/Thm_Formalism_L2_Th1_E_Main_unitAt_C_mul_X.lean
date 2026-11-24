-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Main_unitAt_C_mul_X
-- name    : Formalism.L2.Th1.E.Main.unitAt_C_mul_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:53.138919+00:00
-- url     : https://prove2.me/theorems/5a0e60e0-6482-44f1-95e7-b08954df453f
-- title:
--   Main: unit At C mul X
-- statement:
--   The Main construction uses the unit At C mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXOffOrigin.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXOffOrigin.lean#L22-L23

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

theorem Formalism.L2.Th1.E.Main.unitAt_C_mul_X {a : K} (ha : ‖a‖ = 1) : UnitAt 1 (C a * X : K⟦X⟧) := by sorry
