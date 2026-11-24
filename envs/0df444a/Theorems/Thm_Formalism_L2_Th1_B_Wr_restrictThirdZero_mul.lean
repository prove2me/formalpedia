-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Wr_restrictThirdZero_mul
-- name    : Formalism.L2.Th1.B.Wr.restrictThirdZero_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:01:22.37304+00:00
-- url     : https://prove2.me/theorems/431fd103-0d12-4c72-a97e-0755aa523765
-- title:
--   Wr: restrict Third Zero mul
-- statement:
--   The Wr construction uses the restrict Third Zero mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/XTwoDvdOfRestrictThirdZero.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/XTwoDvdOfRestrictThirdZero.lean#L33-L34

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

theorem Formalism.L2.Th1.B.Wr.restrictThirdZero_mul (f g : MvPowerSeries (Fin 3) K) : ev3 (f * g) = ev3 f * ev3 g := by sorry
