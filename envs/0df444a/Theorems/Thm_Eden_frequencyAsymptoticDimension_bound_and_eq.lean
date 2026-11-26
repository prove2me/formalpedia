-- Prove2me | Theorems.Thm_Eden_frequencyAsymptoticDimension_bound_and_eq
-- name    : Eden.frequencyAsymptoticDimension_bound_and_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:23:09.36077+00:00
-- url     : https://prove2.me/theorems/e4f6bbfb-cbdc-5839-94d4-23096f664928
-- title:
--   Eden: frequency Asymptotic Dimension bound and eq
-- statement:
--   The limiting maximum and exactly the same torus of maximisers.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L99-L104
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L99-L104

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.frequencyAsymptoticDimension_bound_and_eq {c : ℝ} (hc : 4 < c)
    (ν : ℝ) {p : PhaseSpace} (hp : p ∈ attractor) :
    frequencyAsymptoticDimension c ν p ≤ targetDimension c ∧
      (frequencyAsymptoticDimension c ν p = targetDimension c ↔ p ∈ torus) := by sorry
