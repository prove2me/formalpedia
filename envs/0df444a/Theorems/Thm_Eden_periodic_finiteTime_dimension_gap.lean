-- Prove2me | Theorems.Thm_Eden_periodic_finiteTime_dimension_gap
-- name    : Eden.periodic_finiteTime_dimension_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:23:34.80519+00:00
-- url     : https://prove2.me/theorems/40586de3-ccf4-5f09-ba6b-a85ab034628b
-- title:
--   Eden: periodic finite Time dimension gap
-- statement:
--   The Eden construction uses the periodic finite Time dimension gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L55-L61
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L55-L61

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.periodic_finiteTime_dimension_gap {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    sSup (finiteTimeDimension c t '' periodicEquilibriumSet c) <
      globalLyapunovDimension c attractor := by sorry
