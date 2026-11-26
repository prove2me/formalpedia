-- Prove2me | Theorems.Thm_Eden_total_rate_le
-- name    : Eden.total_rate_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:00:55.525261+00:00
-- url     : https://prove2.me/theorems/9132b5be-deb5-46d7-92a0-ddea44801ae6
-- title:
--   Eden: total rate le
-- statement:
--   The Eden construction uses the total rate le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Algebra.lean#L74-L78
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Algebra.lean#L74-L78

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra
set_option autoImplicit true
open Eden

theorem Eden.total_rate_le (s₁ s₂ c : ℝ) :
    radialRate s₁ + tangentialRate s₁ + radialRate s₂ + tangentialRate s₂ - c ≤
      4 - c := by sorry
