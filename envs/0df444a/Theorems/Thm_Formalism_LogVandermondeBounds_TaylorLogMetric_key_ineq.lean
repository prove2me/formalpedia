-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_TaylorLogMetric_key_ineq
-- name    : Formalism.LogVandermondeBounds.TaylorLogMetric.key_ineq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:49:32.505835+00:00
-- url     : https://prove2.me/theorems/df0f7fec-d1be-4fb5-9f46-76fa970efd9a
-- title:
--   Taylor Log Metric: key ineq
-- statement:
--   The Taylor Log Metric construction uses the key ineq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/TaylorLogMetric.lean#L7-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/TaylorLogMetric.lean#L7-L55

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

theorem Formalism.LogVandermondeBounds.TaylorLogMetric.key_ineq (x : ℚ) (hx : 2 ≤ x) :
    ∀ i j : ℕ, i ≤ j → (i, j) ≠ (0, 0) →
      x ^ 3 - 2 * x ^ 2 + 3 ≤ (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) := by sorry
