-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Ph_integral_neg_lU
-- name    : Formalism.L2.Th1.B.Ph.integral_neg_lU
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:07.172198+00:00
-- url     : https://prove2.me/theorems/4b3bc076-e11d-4863-83af-aef199d53471
-- title:
--   Ph: integral neg l U
-- statement:
--   The Ph construction uses the integral neg l U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/LogSigmaOnePullbackSpec.lean#L233-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/LogSigmaOnePullbackSpec.lean#L233-L237

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Ph
open PowerSeries
open Formalism.DworkPowerSeriesWeights (Integral)

theorem Formalism.L2.Th1.B.Ph.integral_neg_lU {K : Type} [NormedField K] {i : PowerSeries K}
    (hi : Integral (ι := Unit) i) : Integral (ι := Unit) (-lU i) := by sorry
