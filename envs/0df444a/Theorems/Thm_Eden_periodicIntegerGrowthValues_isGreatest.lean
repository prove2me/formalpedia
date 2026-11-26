-- Prove2me | Theorems.Thm_Eden_periodicIntegerGrowthValues_isGreatest
-- name    : Eden.periodicIntegerGrowthValues_isGreatest
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:02.117414+00:00
-- url     : https://prove2.me/theorems/cc4f5c50-5d07-56e4-a5e7-4c6c4b8fa1ce
-- title:
--   Eden: periodic Integer Growth Values is Greatest
-- statement:
--   Every integer product maximum is attained on a unit periodic circle, including
--   t=0.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L76-L103
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L76-L103

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.periodicIntegerGrowthValues_isGreatest {c t : ℝ} (hc : 4 < c)
    (ht : 0 ≤ t) {k : ℕ} (hk : k ≤ 5) :
    IsGreatest (periodicIntegerGrowthValues c k t)
      (Real.exp (t * spectrumPartialSum ![2, 0, -2, -2, -c] k)) := by sorry
