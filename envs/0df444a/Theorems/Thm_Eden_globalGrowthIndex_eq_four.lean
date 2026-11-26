-- Prove2me | Theorems.Thm_Eden_globalGrowthIndex_eq_four
-- name    : Eden.globalGrowthIndex_eq_four
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:49:51.578785+00:00
-- url     : https://prove2.me/theorems/f07f08f8-2637-5508-8d89-24cd79715419
-- title:
--   Eden: global Growth Index eq four
-- statement:
--   The largest nonnegative integer global sum has index four when c>4.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L71-L80
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L71-L80

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.globalGrowthIndex_eq_four {c : ℝ} (hc : 4 < c) :
    kaplanYorkeIndex (globalGrowthIncrements c) = 4 := by sorry
