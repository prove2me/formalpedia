-- Prove2me | Theorems.Thm_Formalism_LogFactorialMertensBounds_lip_upto
-- name    : Formalism.LogFactorialMertensBounds.lip_upto
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:06.51506+00:00
-- url     : https://prove2.me/theorems/ae022902-2959-4702-a0bc-67599a522394
-- title:
--   Log Factorial Mertens Bounds: lip upto
-- statement:
--   The Log Factorial Mertens Bounds construction uses the lip upto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L185-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L185-L215

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

theorem Formalism.LogFactorialMertensBounds.lip_upto (k : ℕ) : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ k + 1 → 1 / 2 ≤ y → y ≤ k + 1 →
    |Gz y - Gz x| ≤ K0 * |y - x| := by sorry
