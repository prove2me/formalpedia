-- Prove2me | Theorems.Thm_Eden_globalGrowthRate_eq_inf
-- name    : Eden.globalGrowthRate_eq_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:38.78291+00:00
-- url     : https://prove2.me/theorems/d1f63aa3-3278-5ac5-a833-ac7667a6cc78
-- title:
--   Eden: global Growth Rate eq inf
-- statement:
--   For c≥4 and k≤5, the rate is the infimum over all positive real times.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthLimits.lean#L28-L31
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthLimits.lean#L28-L31

import Definitions.Def_Eden_RealSubadditive
import Definitions.Def_Eden_GlobalGrowthLimits
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.globalGrowthRate_eq_inf {k : ℕ} (hk : k ≤ 5) {c : ℝ} (hc : 4 ≤ c) :
    globalGrowthRate c k =
      sInf ((fun T : ℝ => globalLogGrowth c k T / T) '' Ioi 0) := by sorry
