-- Prove2me | Theorems.Thm_Eden_globalGrowthRate_five
-- name    : Eden.globalGrowthRate_five
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:33.486551+00:00
-- url     : https://prove2.me/theorems/36012a1a-83bf-5f02-abd0-0ba077af4dfa
-- title:
--   Eden: global Growth Rate five
-- statement:
--   The ordinary real-time fifth global growth rate is 4-c for c≥4.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L59-L63
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L59-L63

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.globalGrowthRate_five {c : ℝ} (hc : 4 ≤ c) : globalGrowthRate c 5 = 4 - c := by sorry
