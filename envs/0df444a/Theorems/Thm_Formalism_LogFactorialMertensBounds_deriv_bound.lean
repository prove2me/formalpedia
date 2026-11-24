-- Prove2me | Theorems.Thm_Formalism_LogFactorialMertensBounds_deriv_bound
-- name    : Formalism.LogFactorialMertensBounds.deriv_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:08.400576+00:00
-- url     : https://prove2.me/theorems/943f8aa5-f2e3-41fa-afc7-e3bc5a8af64c
-- title:
--   Log Factorial Mertens Bounds: deriv bound
-- statement:
--   The Log Factorial Mertens Bounds construction uses the deriv bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L139-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L139-L163

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

theorem Formalism.LogFactorialMertensBounds.deriv_bound (k : ℕ) (x : ℝ) (hx1 : (k:ℝ) ≤ x) (hx1' : 1 / 2 ≤ x) (hx2 : x ≤ k + 1) :
    |A k - Real.log x + Real.eulerMascheroniConstant| ≤ K0 := by sorry
