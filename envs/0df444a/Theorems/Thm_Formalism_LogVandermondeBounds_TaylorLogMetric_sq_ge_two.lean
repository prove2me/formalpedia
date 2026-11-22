-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_TaylorLogMetric_sq_ge_two
-- name    : Formalism.LogVandermondeBounds.TaylorLogMetric.sq_ge_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:21.614595+00:00
-- url     : https://prove2.me/theorems/ffcbd498-80c6-4c8e-b0d1-463179edc2e6
-- title:
--   Taylor Log Metric: sq ge two
-- statement:
--   The Taylor Log Metric construction uses the sq ge two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/TaylorLogMetric.lean#L57-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/TaylorLogMetric.lean#L57-L57

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

theorem Formalism.LogVandermondeBounds.TaylorLogMetric.sq_ge_two (p : ℕ) (hp : 2 ≤ p) : 2 ≤ p ^ 2 := by sorry
