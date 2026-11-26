-- Prove2me | Theorems.Thm_Eden_radialRate_eq_q_add
-- name    : Eden.radialRate_eq_q_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:04:48.781508+00:00
-- url     : https://prove2.me/theorems/bf937439-14b4-5b53-b4bd-dd3709274890
-- title:
--   Eden: radial Rate eq q add
-- statement:
--   The Eden construction uses the radial Rate eq q add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Algebra.lean#L23-L26
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Algebra.lean#L23-L26

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra
set_option autoImplicit true
open Eden

theorem Eden.radialRate_eq_q_add (s : ℝ) :
    radialRate s = q s + 2 * s * (-2 * s + 3) := by sorry
