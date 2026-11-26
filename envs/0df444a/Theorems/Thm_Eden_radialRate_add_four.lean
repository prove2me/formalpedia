-- Prove2me | Theorems.Thm_Eden_radialRate_add_four
-- name    : Eden.radialRate_add_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:00:45.304116+00:00
-- url     : https://prove2.me/theorems/478d8278-646c-4acd-9751-f414e483833f
-- title:
--   Eden: radial Rate add four
-- statement:
--   The Eden construction uses the radial Rate add four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Algebra.lean#L28-L31
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Algebra.lean#L28-L31

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra
set_option autoImplicit true
open Eden

theorem Eden.radialRate_add_four (s : ℝ) :
    radialRate s + 4 = (2 - s) * (5 * s + 1) := by sorry
