-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeFiniteVariance_allocation
-- name    : ActuarialValuation.wholeLifeFiniteVariance_allocation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:10:46.378652+00:00
-- url     : https://prove2.me/theorems/047675df-576e-46dc-b184-c9ec7867008b
-- title:
--   Finite-horizon Hattendorff allocation over countable death outcomes
-- statement:
--   Expanding the squared finite sum and using zero cross-year moments eliminates mixed terms. Each diagonal innovation contributes the death mass times conditional year survival, weighted by the square of the corresponding discounted amount at risk.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_n^2]=\sum_{t<n}\rho_t^2 w_t p_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeFiniteInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

namespace ActuarialValuation

theorem wholeLifeFiniteVariance_allocation (w rho : ℕ → ℝ) (n : ℕ)
  (hw : Summable w)
  (hS : ∀ t, 0 < wholeLifeTailMass w t) :
  (∑' k : ℕ, w k * (wholeLifeFiniteInnovation w rho n k) ^ 2) =
    ∑ t ∈ Finset.range n,
      (rho t) ^ 2 * w t *
        (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t) := by sorry

end ActuarialValuation
