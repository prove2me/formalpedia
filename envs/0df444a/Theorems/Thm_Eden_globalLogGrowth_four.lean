-- Prove2me | Theorems.Thm_Eden_globalLogGrowth_four
-- name    : Eden.globalLogGrowth_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:40:40.830507+00:00
-- url     : https://prove2.me/theorems/8e9358ed-e299-57cf-9f24-156a74b4cefd
-- title:
--   Eden: global Log Growth four
-- statement:
--   The fourth logarithmic spatial supremum equals 4t, including t=0.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L38-L41
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L38-L41

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.globalLogGrowth_four {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t) :
    globalLogGrowth c 4 t = 4 * t := by sorry
