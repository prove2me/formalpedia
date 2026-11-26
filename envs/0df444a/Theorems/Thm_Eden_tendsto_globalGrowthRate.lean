-- Prove2me | Theorems.Thm_Eden_tendsto_globalGrowthRate
-- name    : Eden.tendsto_globalGrowthRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:41.018022+00:00
-- url     : https://prove2.me/theorems/2e0336a5-a69e-5edd-800e-60370c37f205
-- title:
--   Eden: tendsto global Growth Rate
-- statement:
--   Ordinary convergence through all real times for c≥4 and k≤5.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthLimits.lean#L34-L38
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthLimits.lean#L34-L38

import Definitions.Def_Eden_RealSubadditive
import Definitions.Def_Eden_GlobalGrowthLimits
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.tendsto_globalGrowthRate {k : ℕ} (hk : k ≤ 5) {c : ℝ} (hc : 4 ≤ c) :
    Tendsto (fun t : ℝ => globalLogGrowth c k t / t) atTop
      (𝓝 (globalGrowthRate c k)) := by sorry
