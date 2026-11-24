-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Wr_restrictThirdZero_eq_rescale
-- name    : Formalism.L2.Th1.B.Wr.restrictThirdZero_eq_rescale
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:00:43.353822+00:00
-- url     : https://prove2.me/theorems/033e3ed3-2ee1-4de7-bf0d-f57df3b5940d
-- title:
--   Wr: restrict Third Zero eq rescale
-- statement:
--   The Wr construction uses the restrict Third Zero eq rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/XTwoDvdOfRestrictThirdZero.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/XTwoDvdOfRestrictThirdZero.lean#L20-L25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_XTwoDvdOfRestrictThirdZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Wr
open MvPowerSeries
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.Wr.restrictThirdZero_eq_rescale (h : MvPowerSeries (Fin 3) K) : ev3 h = rescale ![1, 1, 0] h := by sorry
