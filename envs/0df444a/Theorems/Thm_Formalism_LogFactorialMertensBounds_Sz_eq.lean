-- Prove2me | Theorems.Thm_Formalism_LogFactorialMertensBounds_Sz_eq
-- name    : Formalism.LogFactorialMertensBounds.Sz_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:09.870852+00:00
-- url     : https://prove2.me/theorems/d4be2cb3-9006-4ec1-bb8e-febce7e0f460
-- title:
--   Log Factorial Mertens Bounds: Sz eq
-- statement:
--   The Log Factorial Mertens Bounds construction uses the Sz eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L107-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L107-L125

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

theorem Formalism.LogFactorialMertensBounds.Sz_eq (k : ℕ) (x : ℝ) (hx1 : (k:ℝ) ≤ x) (hx2 : x ≤ k + 1) :
    Sz x = x * A k - ∑ n ∈ Finset.Ioc 0 k, Λ n := by sorry
