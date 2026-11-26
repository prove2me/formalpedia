-- Prove2me | Theorems.Thm_Eden_periodicGlobalGrowthInterpolation_integer
-- name    : Eden.periodicGlobalGrowthInterpolation_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:03:44.431284+00:00
-- url     : https://prove2.me/theorems/0e3d9fa0-e6b4-46b8-a414-2941f20091cf
-- title:
--   Eden: periodic Global Growth Interpolation integer
-- statement:
--   Equality with the global sums at all six integer nodes.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalDimension.lean#L40-L44
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalDimension.lean#L40-L44

import Definitions.Def_Eden_PeriodicGlobalGrowth
import Definitions.Def_Eden_PeriodicGlobalDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.periodicGlobalGrowthInterpolation_integer {c : ℝ} (hc : 4 < c)
    {k : ℕ} (hk : k ≤ 5) :
    periodicGlobalGrowthInterpolation c k = periodicGlobalGrowthRate c k := by sorry
