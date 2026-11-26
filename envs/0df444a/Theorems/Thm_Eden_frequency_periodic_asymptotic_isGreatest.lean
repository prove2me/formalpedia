-- Prove2me | Theorems.Thm_Eden_frequency_periodic_asymptotic_isGreatest
-- name    : Eden.frequency_periodic_asymptotic_isGreatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:25:00.234629+00:00
-- url     : https://prove2.me/theorems/b681d2b4-2bfe-5dee-baed-f3325c66c63f
-- title:
--   Eden: frequency periodic asymptotic is Greatest
-- statement:
--   The limiting dimension maximum is attained among nonstationary periodic points.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RationalFrequency.lean#L83-L91
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RationalFrequency.lean#L83-L91

import Definitions.Def_Eden_FrequencyDimensions
import Definitions.Def_Eden_FrequencyAttractor
import Definitions.Def_Eden_FrequencyUniqueness
import Mathlib.Topology.Instances.Rat
import Definitions.Def_Eden_RationalFrequency
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.frequency_periodic_asymptotic_isGreatest {c : ℝ} (hc : 4 < c) (ν : ℚ) :
    IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν)
      (targetDimension c) := by sorry
