-- Prove2me | Theorems.Thm_ActuarialValuation_flatInterest_geometric_sum
-- name    : ActuarialValuation.flatInterest_geometric_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:40:33.564266+00:00
-- url     : https://prove2.me/theorems/e4ffae7e-e09d-4285-8549-d65a85501ea1
-- title:
--   Flat interest geometric sum
-- statement:
--   States the finite geometric-sum formula for discounting payments at times 0 through m under a positive flat rate.
--
--   **Mathematical statement**
--
--   $$
--   \sum_{k=0}^{m}v^k=\frac{1+i}{i}(1-v^{m+1})
--   $$
-- source:
--   Life Contingencies Chapter 3 §3.3.1 equations (3.13)-(3.14), with §3.2.1 (3.7) and derived supporting mathematics; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
open MeasureTheory

namespace ActuarialValuation

theorem flatInterest_geometric_sum (i : ℝ) (hi : 0 < i) (m : ℕ)
    :
    (∑ k ∈ Finset.range (m + 1), (1 / (1 + i) : ℝ) ^ k) =
      ((1 + i) / i) * (1 - (1 / (1 + i) : ℝ) ^ (m + 1)) := by sorry

end ActuarialValuation
