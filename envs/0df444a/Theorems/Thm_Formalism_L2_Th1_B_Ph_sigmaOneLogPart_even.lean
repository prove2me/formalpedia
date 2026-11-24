-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Ph_sigmaOneLogPart_even
-- name    : Formalism.L2.Th1.B.Ph.sigmaOneLogPart_even
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:19.113158+00:00
-- url     : https://prove2.me/theorems/623b906c-bd84-4e9a-86e2-c11bba68f9df
-- title:
--   Ph: sigma One Log Part even
-- statement:
--   The Ph construction uses the sigma One Log Part even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/LogSigmaOnePullbackSpec.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/LogSigmaOnePullbackSpec.lean#L90-L96

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

theorem Formalism.L2.Th1.B.Ph.sigmaOneLogPart_even (e1 kap : K) {w : PowerSeries K} (hw : ∀ n, Odd n → coeff n w = 0) :
    ∀ n, Odd n → coeff n (sigmaOneSeries e1 kap w) = 0 := by sorry
