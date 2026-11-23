-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_mul_pd_fLog
-- name    : Formalism.L2.Th1.B.mul_pd_fLog
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:03.133007+00:00
-- url     : https://prove2.me/theorems/aabf4a78-0d14-4602-b133-992dfe4881e4
-- title:
--   B: mul pd f Log
-- statement:
--   The B construction uses the mul pd f Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/OneAddMulDerivLogSubst.lean#L260-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/OneAddMulDerivLogSubst.lean#L260-L269

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open PowerSeries
variable {K : Type} [Field K] [CharZero K] {ι : Type}

theorem Formalism.L2.Th1.B.mul_pd_fLog [Finite ι] (i : ι) {g : MvPowerSeries ι K}
    (hg : MvPowerSeries.constantCoeff g = 1) : g * pd i (fLog g) = pd i g := by sorry
