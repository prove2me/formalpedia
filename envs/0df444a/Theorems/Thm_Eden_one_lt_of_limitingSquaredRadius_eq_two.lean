-- Prove2me | Theorems.Thm_Eden_one_lt_of_limitingSquaredRadius_eq_two
-- name    : Eden.one_lt_of_limitingSquaredRadius_eq_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:14.956698+00:00
-- url     : https://prove2.me/theorems/1bf5f607-92aa-5016-a265-4d7ac3641d6e
-- title:
--   Eden: one lt of limiting Squared Radius eq two
-- statement:
--   The Eden construction uses the one lt of limiting Squared Radius eq two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LimitingInterpolation.lean#L48-L53
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LimitingInterpolation.lean#L48-L53

import Definitions.Def_Eden_InterpolationSign
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_LimitingInterpolation
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.one_lt_of_limitingSquaredRadius_eq_two {s : ℝ}
    (hs : limitingSquaredRadius s = 2) : 1 < s := by sorry
