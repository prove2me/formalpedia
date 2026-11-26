-- Prove2me | Theorems.Thm_Eden_periodicGlobalGrowthInterpolation_isGreatest
-- name    : Eden.periodicGlobalGrowthInterpolation_isGreatest
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:07.218201+00:00
-- url     : https://prove2.me/theorems/e2ba0bbc-85bc-541e-b846-fd50b8f9d710
-- title:
--   Eden: periodic Global Growth Interpolation is Greatest
-- statement:
--   The maximum is over all real dimensions in [0,5], including the zero at three.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalDimension.lean#L68-L80
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalDimension.lean#L68-L80

import Definitions.Def_Eden_PeriodicGlobalGrowth
import Definitions.Def_Eden_PeriodicGlobalDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.periodicGlobalGrowthInterpolation_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ periodicGlobalGrowthInterpolation c d} 3 := by sorry
