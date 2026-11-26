-- Prove2me | Theorems.Thm_Eden_globalGrowthInterpolation_isGreatest
-- name    : Eden.globalGrowthInterpolation_isGreatest
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:41:46.780802+00:00
-- url     : https://prove2.me/theorems/ad68e536-24c9-48bf-8530-7c017347713e
-- title:
--   Eden: global Growth Interpolation is Greatest
-- statement:
--   The full real interpolant has greatest nonnegative point 4+4/c when c>4.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L83-L104
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean#L83-L104

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.globalGrowthInterpolation_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ globalGrowthInterpolation c d}
      (targetDimension c) := by sorry
