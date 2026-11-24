-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_exp_biv
-- name    : Formalism.L2.Th1.B.exp_biv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:48.506256+00:00
-- url     : https://prove2.me/theorems/ccbd9cec-a4ca-40ff-898f-f9f1732f7ab3
-- title:
--   B: exp biv
-- statement:
--   The B construction uses the exp biv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/OneAddMulDerivLogSubst.lean#L175-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/OneAddMulDerivLogSubst.lean#L175-L191

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
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.exp_biv :
    (exp K).subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
      (exp K).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) *
        (exp K).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by sorry
