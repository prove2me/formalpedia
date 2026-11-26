-- Prove2me | Theorems.Thm_Eden_finiteTimeDimension_periodic_isGreatest
-- name    : Eden.finiteTimeDimension_periodic_isGreatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:57.158986+00:00
-- url     : https://prove2.me/theorems/bacbc812-13e0-4f43-8cf9-904084ad51c1
-- title:
--   Eden: finite Time Dimension periodic is Greatest
-- statement:
--   For every positive real time the largest local dimension on the full
--   periodic/equilibrium set is exactly three and is attained.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L30-L37
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L30-L37

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.finiteTimeDimension_periodic_isGreatest {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    IsGreatest (finiteTimeDimension c t '' periodicEquilibriumSet c) 3 := by sorry
