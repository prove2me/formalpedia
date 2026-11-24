-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_dz_X_pow
-- name    : Formalism.L2.Th1.B.dz_X_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:55:31.488797+00:00
-- url     : https://prove2.me/theorems/2a759b05-1e3a-4a27-9626-024191cce0a2
-- title:
--   B: dz X pow
-- statement:
--   The B construction uses the dz X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/WeierstrassReducedEquations.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/WeierstrassReducedEquations.lean#L52-L58

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
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

theorem Formalism.L2.Th1.B.dz_X_pow (n : ℕ) : dz ((X : PowerSeries K) ^ (n + 1)) = ((n : PowerSeries K) + 1) * X ^ n := by sorry
