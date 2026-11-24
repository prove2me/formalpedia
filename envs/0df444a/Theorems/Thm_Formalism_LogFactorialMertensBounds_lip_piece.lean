-- Prove2me | Theorems.Thm_Formalism_LogFactorialMertensBounds_lip_piece
-- name    : Formalism.LogFactorialMertensBounds.lip_piece
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:52:34.278079+00:00
-- url     : https://prove2.me/theorems/105497d3-8eb7-4319-ab18-64f119b5f1e9
-- title:
--   Log Factorial Mertens Bounds: lip piece
-- statement:
--   The Log Factorial Mertens Bounds construction uses the lip piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L165-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L165-L183

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

theorem Formalism.LogFactorialMertensBounds.lip_piece (k : ℕ) (x y : ℝ) (hx1 : (k:ℝ) ≤ x) (hx1' : 1 / 2 ≤ x) (hx2 : x ≤ k + 1)
    (hy1 : (k:ℝ) ≤ y) (hy1' : 1 / 2 ≤ y) (hy2 : y ≤ k + 1) :
    |Gz y - Gz x| ≤ K0 * |y - x| := by sorry
