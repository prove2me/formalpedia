-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Power_sum_zero
-- name    : Formalism.L2.Th1.E.Power.sum_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:41.340126+00:00
-- url     : https://prove2.me/theorems/fc263df5-0df3-4b8c-9c08-e2c5260236f9
-- title:
--   Power: sum zero
-- statement:
--   The Power construction uses the sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L79-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L79-L92

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

theorem Formalism.L2.Th1.E.Power.sum_zero {A : Type} [AddCommGroup A] [Finite A] (M₀ : A → ℝ) (Q : A) (c : ℝ)
    (h : ∀ P : A, M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P = 2 * c) : c = 0 := by sorry
