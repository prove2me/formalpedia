-- Prove2me | Theorems.Thm_Eden_total_rate_neg
-- name    : Eden.total_rate_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:05:31.132432+00:00
-- url     : https://prove2.me/theorems/0a5d131d-24cc-598d-b254-a77e26a53229
-- title:
--   Eden: total rate neg
-- statement:
--   The Eden construction uses the total rate neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Algebra.lean#L80-L82
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Algebra.lean#L80-L82

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra
set_option autoImplicit true
open Eden

theorem Eden.total_rate_neg (s₁ s₂ : ℝ) {c : ℝ} (hc : 4 < c) :
    radialRate s₁ + tangentialRate s₁ + radialRate s₂ + tangentialRate s₂ - c < 0 := by sorry
