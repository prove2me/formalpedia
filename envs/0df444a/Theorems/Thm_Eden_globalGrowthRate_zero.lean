-- Prove2me | Theorems.Thm_Eden_globalGrowthRate_zero
-- name    : Eden.globalGrowthRate_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:41:14.021865+00:00
-- url     : https://prove2.me/theorems/0583b8d3-3895-53e7-b882-8df0a130d8ad
-- title:
--   Eden: global Growth Rate zero
-- statement:
--   The Eden construction uses the global Growth Rate zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L71-L75
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L71-L75

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.globalGrowthRate_zero {c : ℝ} (hc : 4 ≤ c) : globalGrowthRate c 0 = 0 := by sorry
