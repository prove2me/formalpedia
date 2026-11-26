-- Prove2me | Theorems.Thm_Eden_frequency_periodic_finiteTime_isGreatest
-- name    : Eden.frequency_periodic_finiteTime_isGreatest
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:25:32.957494+00:00
-- url     : https://prove2.me/theorems/16d83ca8-7246-583b-8983-7e12c9465bc2
-- title:
--   Eden: frequency periodic finite Time is Greatest
-- statement:
--   The finite-time maximum is likewise attained on periodic points at every
--   positive time.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RationalFrequency.lean#L95-L104
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RationalFrequency.lean#L95-L104

import Definitions.Def_Eden_FrequencyDimensions
import Definitions.Def_Eden_FrequencyAttractor
import Definitions.Def_Eden_FrequencyUniqueness
import Mathlib.Topology.Instances.Rat
import Definitions.Def_Eden_RationalFrequency
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.frequency_periodic_finiteTime_isGreatest {c t : ℝ} (hc : 4 < c)
    (ν : ℚ) (ht : 0 < t) :
    IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν)
      (targetDimension c) := by sorry
