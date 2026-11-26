-- Prove2me | Theorems.Thm_Eden_commonIndexLocalDimension_periodic_isGreatest
-- name    : Eden.commonIndexLocalDimension_periodic_isGreatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:40.8808+00:00
-- url     : https://prove2.me/theorems/92489e86-a4bd-5779-ad4e-135401321a8a
-- title:
--   Eden: common Index Local Dimension periodic is Greatest
-- statement:
--   Over the entire equilibrium/periodic set, the fixed global index gives
--   maximum 4-2/c, attained on a unit circle.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L75-L88
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L75-L88

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.commonIndexLocalDimension_periodic_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest (commonIndexLocalDimension c '' periodicEquilibriumSet c) (4 - 2 / c) := by sorry
