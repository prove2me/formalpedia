-- Prove2me | Theorems.Thm_EdenVerified_s05_real_time_limit
-- name    : EdenVerified.s05_real_time_limit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:22:16.291354+00:00
-- url     : https://prove2.me/theorems/c977253b-ff57-509f-8ed2-73513e97887d
-- title:
--   Eden Verified: s05 real time limit
-- statement:
--   The limit runs through real time and equals the infimum over all positive real
--   times.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L217-L221
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L217-L221

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s05_real_time_limit (c : ℝ) (hc : 4 < c) (k : ℕ) (hk : k ≤ 5) :
    Tendsto (fun t : ℝ => globalLogGrowth c k t / t) atTop
      (𝓝 (globalGrowthRate c k)) ∧
    globalGrowthRate c k = sInf ((fun T : ℝ => globalLogGrowth c k T / T) '' Ioi 0) := by sorry
