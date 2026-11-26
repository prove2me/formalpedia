-- Prove2me | Theorems.Thm_Eden_globalLogGrowth_five
-- name    : Eden.globalLogGrowth_five
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:41:30.865532+00:00
-- url     : https://prove2.me/theorems/5eba37a4-7967-4a01-a73c-2c10040f8c96
-- title:
--   Eden: global Log Growth five
-- statement:
--   The fifth logarithmic spatial supremum equals (4-c)t, including t=0.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L44-L49
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L44-L49

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.globalLogGrowth_five {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t) :
    globalLogGrowth c 5 t = (4 - c) * t := by sorry
