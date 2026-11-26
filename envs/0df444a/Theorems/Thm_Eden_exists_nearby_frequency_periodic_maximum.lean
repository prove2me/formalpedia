-- Prove2me | Theorems.Thm_Eden_exists_nearby_frequency_periodic_maximum
-- name    : Eden.exists_nearby_frequency_periodic_maximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:57:58.640244+00:00
-- url     : https://prove2.me/theorems/9eb0575f-ee28-45cf-8b8b-66a3f0bef4fe
-- title:
--   Eden: exists nearby frequency periodic maximum
-- statement:
--   Arbitrarily small positive-rational frequency changes restore periodic
--   attainment.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RationalFrequency.lean#L120-L129
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RationalFrequency.lean#L120-L129

import Definitions.Def_Eden_FrequencyDimensions
import Definitions.Def_Eden_FrequencyAttractor
import Definitions.Def_Eden_FrequencyUniqueness
import Mathlib.Topology.Instances.Rat
import Definitions.Def_Eden_RationalFrequency
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exists_nearby_frequency_periodic_maximum {c ε : ℝ} (hc : 4 < c) (hε : 0 < ε) :
    ∃ ν : ℚ, 0 < ν ∧ |(ν : ℝ) - Real.sqrt 2| < ε ∧
      IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν)
        (targetDimension c) ∧
      ∀ t : ℝ, 0 < t →
        IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν)
          (targetDimension c) := by sorry
