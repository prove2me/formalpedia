-- Prove2me | Theorems.Thm_ActuarialValuation_decrementMultipleCauseVariance_fundamental
-- name    : ActuarialValuation.decrementMultipleCauseVariance_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:15:19.825987+00:00
-- url     : https://prove2.me/theorems/2f5b6227-e2c1-4679-ab96-ddf1f53314e1
-- title:
--   Finite-horizon Hattendorff identity with multiple decrement causes
-- statement:
--   The capstone allocates the second moment of the finite-horizon centred reserve loss across successive policy years. Within each year it retains all cause-specific negative covariance contributions, while cross-year innovations are orthogonal. The lifetime remains genuinely countable in possible termination dates.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_n^2]=\sum_{t<n}\big[\sum_cw_{t,c}\rho_{t,c}^2-(\sum_cw_{t,c}\rho_{t,c})^2/S_t\big]
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementFiniteExposure
import Definitions.Def_actuarial_decrementAnnualRisk
import Definitions.Def_actuarial_decrementTailMass
import Definitions.Def_actuarial_decrementYearMass

namespace ActuarialValuation

theorem decrementMultipleCauseVariance_fundamental {C : Type*} [Fintype C]
  (w rho : ℕ → C → ℝ) (n : ℕ)
  (hw : Summable (fun k : ℕ => decrementYearMass w k))
  (hn : ∀ k e, 0 ≤ w k e)
  (hS : ∀ t, 0 < decrementTailMass w t)
  (hTotal : (∑' k : ℕ, decrementYearMass w k) = 1) :
  (∑' k : ℕ, ∑ d : C,
       w k d * (decrementFiniteExposure w rho n k d) ^ 2) =
    ∑ t ∈ Finset.range n, decrementAnnualRisk w rho t := by sorry

end ActuarialValuation
