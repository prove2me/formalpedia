-- Prove2me | Theorems.Thm_Formalism_LogFactorialBounds_sum_div_mul_log_le_log_factorial
-- name    : Formalism.LogFactorialBounds.sum_div_mul_log_le_log_factorial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:01.358734+00:00
-- url     : https://prove2.me/theorems/b8529d32-8ce5-4311-8c96-a0a69b598894
-- title:
--   Log Factorial Bounds: sum div mul log le log factorial
-- statement:
--   The Log Factorial Bounds construction uses the sum div mul log le log factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialBounds/LogFactorialProofs/PrimeSum.lean#L22-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialBounds/LogFactorialProofs/PrimeSum.lean#L22-L61

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

theorem Formalism.LogFactorialBounds.sum_div_mul_log_le_log_factorial (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log (n.factorial : ℕ) := by sorry
