-- Prove2me | Theorems.Thm_EdenVerified_s06_global_interpolation
-- name    : EdenVerified.s06_global_interpolation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:23:03.783622+00:00
-- url     : https://prove2.me/theorems/de92d106-a672-47f5-8043-5f2a44029cc7
-- title:
--   Eden Verified: s06 global interpolation
-- statement:
--   Interpolation uses maximised sums, with all integer endpoints and the attained
--   root.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L236-L249
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L236-L249

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s06_global_interpolation (c : ℝ) (hc : 4 < c) :
    (∀ k : ℕ, k ≤ 5 → globalGrowthInterpolation c k = globalGrowthRate c k) ∧
    (∀ k : ℕ, k < 5 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      globalGrowthInterpolation c ((k : ℝ)+α) =
        (1-α)*globalGrowthRate c k + α*globalGrowthRate c (k+1)) ∧
    kaplanYorkeIndex (globalGrowthIncrements c) = 4 ∧
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ globalGrowthInterpolation c d} (4+4/c) ∧
    globalGrowthDimension c = 4 + globalGrowthRate c 4 /
      (globalGrowthRate c 4 - globalGrowthRate c 5) ∧
    globalGrowthDimension c = 4+4/c := by sorry
