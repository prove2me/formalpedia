-- Prove2me | Theorems.Thm_Formalism_LogFactorialMertensBounds_sum_log_eq
-- name    : Formalism.LogFactorialMertensBounds.sum_log_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:41.752841+00:00
-- url     : https://prove2.me/theorems/65be9627-b464-4440-a7ed-248e338340ee
-- title:
--   Log Factorial Mertens Bounds: sum log eq
-- statement:
--   The Log Factorial Mertens Bounds construction uses the sum log eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L37-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L37-L53

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

theorem Formalism.LogFactorialMertensBounds.sum_log_eq (k : ℕ) :
    ∑ n ∈ Finset.Ioc 0 k, Real.log n = ∑ n ∈ Finset.Ioc 0 k, Λ n * ((k / n : ℕ) : ℝ) := by sorry
