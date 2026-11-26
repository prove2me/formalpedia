-- Prove2me | Theorems.Thm_Eden_globalGrowthRate_four
-- name    : Eden.globalGrowthRate_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:40:31.700126+00:00
-- url     : https://prove2.me/theorems/027eb91d-fa30-54d5-a8af-89f3053458f9
-- title:
--   Eden: global Growth Rate four
-- statement:
--   The ordinary real-time fourth global growth rate is four for c≥4.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L52-L56
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L52-L56

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.globalGrowthRate_four {c : ℝ} (hc : 4 ≤ c) : globalGrowthRate c 4 = 4 := by sorry
