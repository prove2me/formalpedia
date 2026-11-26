-- Prove2me | Theorems.Thm_Eden_globalGrowthDimension_eq_rate_ratio
-- name    : Eden.globalGrowthDimension_eq_rate_ratio
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:49:55.410721+00:00
-- url     : https://prove2.me/theorems/948ecc47-9ad1-59f2-bc1d-33a403768d14
-- title:
--   Eden: global Growth Dimension eq rate ratio
-- statement:
--   The same dimension in the fourth/fifth global-rate ratio form.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L112-L117
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L112-L117

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.globalGrowthDimension_eq_rate_ratio {c : ℝ} (hc : 4 < c) :
    globalGrowthDimension c =
      4 + globalGrowthRate c 4 / (globalGrowthRate c 4 - globalGrowthRate c 5) := by sorry
