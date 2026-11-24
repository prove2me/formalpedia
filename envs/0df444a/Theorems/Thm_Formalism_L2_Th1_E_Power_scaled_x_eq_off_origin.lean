-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Power_scaled_x_eq_off_origin
-- name    : Formalism.L2.Th1.E.Power.scaled_x_eq_off_origin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:35.802951+00:00
-- url     : https://prove2.me/theorems/08de5bd5-b9cd-4315-a998-b3e1925b2562
-- title:
--   Power: scaled x eq off origin
-- statement:
--   The Power construction uses the scaled x eq off origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L65-L69

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

theorem Formalism.L2.Th1.E.Power.scaled_x_eq_off_origin {K : Type} [Field K] (W : WeierstrassCurve K) (P : W.toAffine.Point) (hP : P ≠ 0) :
    x2 W P = X ^ 2 * xT W P := by sorry
