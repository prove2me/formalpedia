-- Prove2me | Theorems.Thm_EdenVerified_s06_exact_global_rates
-- name    : EdenVerified.s06_exact_global_rates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:22:57.341149+00:00
-- url     : https://prove2.me/theorems/6a440dfa-c668-462f-b71c-90d2dca9e99b
-- title:
--   Eden Verified: s06 exact global rates
-- statement:
--   Exact finite-time fourth/fifth growth and all required signs of their limits.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L224-L232
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L224-L232

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s06_exact_global_rates (c : ℝ) (hc : 4 < c) :
    (∀ t : ℝ, 0 ≤ t → globalLogGrowth c 4 t = 4*t ∧
      globalLogGrowth c 5 t = (4-c)*t) ∧
    globalGrowthRate c 0 = 0 ∧
    (∀ k : ℕ, k ≤ 4 → 0 ≤ globalGrowthRate c k) ∧
    globalGrowthRate c 4 = 4 ∧ globalGrowthRate c 5 = 4-c ∧ globalGrowthRate c 5 < 0 := by sorry
