-- Prove2me | Theorems.Thm_Formalism_LogFactorialBounds_log_factorial_le
-- name    : Formalism.LogFactorialBounds.log_factorial_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:14.504638+00:00
-- url     : https://prove2.me/theorems/f3057548-b2ba-4c52-8bed-1997363b40eb
-- title:
--   Log Factorial Bounds: log factorial le
-- statement:
--   The Log Factorial Bounds construction uses the log factorial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialBounds/LogFactorialProofs/PrimeSum.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialBounds/LogFactorialProofs/PrimeSum.lean#L63-L69

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

theorem Formalism.LogFactorialBounds.log_factorial_le (n : ℕ) : Real.log (n.factorial : ℕ) ≤ n * Real.log n := by sorry
