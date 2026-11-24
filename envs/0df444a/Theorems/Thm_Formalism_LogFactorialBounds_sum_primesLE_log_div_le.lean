-- Prove2me | Theorems.Thm_Formalism_LogFactorialBounds_sum_primesLE_log_div_le
-- name    : Formalism.LogFactorialBounds.sum_primesLE_log_div_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:15.656814+00:00
-- url     : https://prove2.me/theorems/37d9a4f8-f82c-4457-a54a-24d6592764e3
-- title:
--   Log Factorial Bounds: sum primes LE log div le
-- statement:
--   The Log Factorial Bounds construction uses the sum primes LE log div le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialBounds/LogFactorialProofs/PrimeSum.lean#L71-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialBounds/LogFactorialProofs/PrimeSum.lean#L71-L116

import Definitions.Def_Formalism_LogFactorialBounds_LocalFactorSplitDv
import Mathlib
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LogFactorialBounds
open Finset Real

theorem Formalism.LogFactorialBounds.sum_primesLE_log_div_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by sorry
