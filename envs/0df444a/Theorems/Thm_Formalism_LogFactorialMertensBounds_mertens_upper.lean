-- Prove2me | Theorems.Thm_Formalism_LogFactorialMertensBounds_mertens_upper
-- name    : Formalism.LogFactorialMertensBounds.mertens_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:40.568404+00:00
-- url     : https://prove2.me/theorems/fc1ecfb6-2464-4c00-be59-fa3c4b15accc
-- title:
--   Log Factorial Mertens Bounds: mertens upper
-- statement:
--   The Log Factorial Mertens Bounds construction uses the mertens upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L55-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L55-L84

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

theorem Formalism.LogFactorialMertensBounds.mertens_upper (k : ℕ) (hk : 1 ≤ k) : A k ≤ Real.log k + (Real.log 4 + 4) := by sorry
