-- Prove2me | Theorems.Thm_Eden_globalGrowthRate_five_neg
-- name    : Eden.globalGrowthRate_five_neg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:41:20.277413+00:00
-- url     : https://prove2.me/theorems/77e0b45b-37d2-5db3-aa73-a2039d907446
-- title:
--   Eden: global Growth Rate five neg
-- statement:
--   The Eden construction uses the global Growth Rate five neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L103-L105
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L103-L105

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.globalGrowthRate_five_neg {c : ℝ} (hc : 4 < c) : globalGrowthRate c 5 < 0 := by sorry
