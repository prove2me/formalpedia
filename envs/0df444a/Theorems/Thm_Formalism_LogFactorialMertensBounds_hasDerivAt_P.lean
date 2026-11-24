-- Prove2me | Theorems.Thm_Formalism_LogFactorialMertensBounds_hasDerivAt_P
-- name    : Formalism.LogFactorialMertensBounds.hasDerivAt_P
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:52:32.250523+00:00
-- url     : https://prove2.me/theorems/9e72c80e-b2bf-428e-9a5f-b2d695f3722a
-- title:
--   Log Factorial Mertens Bounds: has Deriv At P
-- statement:
--   The Log Factorial Mertens Bounds construction uses the has Deriv At P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L131-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L131-L137

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

theorem Formalism.LogFactorialMertensBounds.hasDerivAt_P (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (P k) (A k - Real.log x + Real.eulerMascheroniConstant) x := by sorry
