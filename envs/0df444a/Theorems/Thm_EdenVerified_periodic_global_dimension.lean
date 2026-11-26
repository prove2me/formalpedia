-- Prove2me | Theorems.Thm_EdenVerified_periodic_global_dimension
-- name    : EdenVerified.periodic_global_dimension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:25:36.287554+00:00
-- url     : https://prove2.me/theorems/5dd4170d-f730-5574-9ece-6372eb3030f5
-- title:
--   Eden Verified: periodic global dimension
-- statement:
--   The full interpolant has index and dimension three, including its neutral node.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L471-L476
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L471-L476

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.periodic_global_dimension (c : ℝ) (hc : 4 < c) :
    kaplanYorkeIndex (periodicGlobalGrowthIncrements c) = 3 ∧
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ periodicGlobalGrowthInterpolation c d} 3 ∧
    periodicGlobalGrowthDimension c = 3 := by sorry
