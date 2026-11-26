-- Prove2me | Theorems.Thm_Eden_globalGrowthDimension_eq_target
-- name    : Eden.globalGrowthDimension_eq_target
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:41:42.194802+00:00
-- url     : https://prove2.me/theorems/d23dc298-e808-49a1-b85f-6de9082f2ce8
-- title:
--   Eden: global Growth Dimension eq target
-- statement:
--   The dimension obtained from maximised sums is exactly 4+4/c.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L107-L109
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L107-L109

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.globalGrowthDimension_eq_target {c : ℝ} (hc : 4 < c) :
    globalGrowthDimension c = 4 + 4 / c := by sorry
