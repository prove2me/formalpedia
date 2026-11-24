-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_fLog
-- name    : Formalism.L2.Th1.B.Ph.psubst_fLog
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:47:50.759549+00:00
-- url     : https://prove2.me/theorems/da72a588-9b00-412c-bff7-6d98df90ad63
-- title:
--   Ph: psubst f Log
-- statement:
--   The Ph construction uses the psubst f Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/LogSigmaOnePullbackSpec.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/LogSigmaOnePullbackSpec.lean#L41-L45

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
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.Ph.psubst_fLog {l g : PowerSeries K} (hl : constantCoeff l = 0) (hg : constantCoeff g = 1) :
    subst l (fLog g) = fLog (subst l g) := by sorry
