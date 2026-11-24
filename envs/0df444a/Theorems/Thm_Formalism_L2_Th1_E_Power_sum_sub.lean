-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Power_sum_sub
-- name    : Formalism.L2.Th1.E.Power.sum_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:35.952843+00:00
-- url     : https://prove2.me/theorems/c5d158bc-3a1c-435c-b0e4-1311505672ae
-- title:
--   Power: sum sub
-- statement:
--   The Power construction uses the sum sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L75-L77

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXEqOffOrigin
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
open Formalism.L2.Th1.E.Power

theorem Formalism.L2.Th1.E.Power.sum_sub {A : Type} [AddCommGroup A] [Fintype A] (M : A → ℝ) (Q : A) :
    ∑ P, M (P - Q) = ∑ P, M P := by sorry
