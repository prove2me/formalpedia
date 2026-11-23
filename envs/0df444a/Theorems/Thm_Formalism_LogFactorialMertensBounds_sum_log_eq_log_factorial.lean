-- Prove2me | Theorems.Thm_Formalism_LogFactorialMertensBounds_sum_log_eq_log_factorial
-- name    : Formalism.LogFactorialMertensBounds.sum_log_eq_log_factorial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:47.423233+00:00
-- url     : https://prove2.me/theorems/39d49fb4-6c1d-4d3e-92ef-44c58eddf128
-- title:
--   Log Factorial Mertens Bounds: sum log eq log factorial
-- statement:
--   The Log Factorial Mertens Bounds construction uses the sum log eq log factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L28-L35

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
noncomputable section
open Formalism
open Formalism.LogFactorialMertensBounds

theorem Formalism.LogFactorialMertensBounds.sum_log_eq_log_factorial (k : ℕ) :
    ∑ n ∈ Finset.Ioc 0 k, Real.log n = Real.log (k.factorial : ℝ) := by sorry
