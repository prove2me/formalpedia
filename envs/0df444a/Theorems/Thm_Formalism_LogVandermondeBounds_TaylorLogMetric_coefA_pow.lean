-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_TaylorLogMetric_coefA_pow
-- name    : Formalism.LogVandermondeBounds.TaylorLogMetric.coefA_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:53:08.946453+00:00
-- url     : https://prove2.me/theorems/794ccfa5-3e91-430e-942b-3114d5920a20
-- title:
--   Taylor Log Metric: coef A pow
-- statement:
--   The Taylor Log Metric construction uses the coef A pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/TaylorLogMetric.lean#L82-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/TaylorLogMetric.lean#L82-L99

import Definitions.Def_Formalism_LogVandermondeBounds_EvenOddPowerQuotientEqualityCases
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.TaylorLogMetric
open Finset

theorem Formalism.LogVandermondeBounds.TaylorLogMetric.coefA_pow (p i j : ℕ) (hp : 2 ≤ p) :
    coefA p ((p ^ 2) ^ i) (p * (p ^ 2) ^ j) = if i ≤ j then 1 / (p : ℚ) ^ (i + j + 1) else 0 := by sorry
