-- Prove2me | Theorems.Thm_Eden_frequencyFiniteTimeDimension_bound_and_eq
-- name    : Eden.frequencyFiniteTimeDimension_bound_and_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:23:07.02248+00:00
-- url     : https://prove2.me/theorems/e5c7ba61-6a13-5f76-a3ca-141593829820
-- title:
--   Eden: frequency Finite Time Dimension bound and eq
-- statement:
--   The finite-time maximum and exactly the same torus of maximisers.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L91-L96
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L91-L96

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.frequencyFiniteTimeDimension_bound_and_eq {c t : ℝ} (hc : 4 < c)
    (ν : ℝ) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor) :
    frequencyFiniteTimeDimension c ν t p ≤ targetDimension c ∧
      (frequencyFiniteTimeDimension c ν t p = targetDimension c ↔ p ∈ torus) := by sorry
