-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeHattendorff_countable_limit
-- name    : ActuarialValuation.wholeLifeHattendorff_countable_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:11:16.588152+00:00
-- url     : https://prove2.me/theorems/bdd89403-8048-40bf-a9d9-d8cca7909c10
-- title:
--   Complete-life Hattendorff variance allocation under summable L² risk
-- statement:
--   The complete-life limit has zero mean and its second moment is the entire infinite sum of annual Hattendorff contributions. This uses countably many possible finite death years, nonnegative unit probability mass, positive survival tails and summability of discounted variance exposures to pass from finite truncations to an L² limit.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_\infty]=0,\quad\mathrm{Var}(Z_\infty)=\sum_{t\ge0}\rho_t^2w_tp_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeCompleteInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

namespace ActuarialValuation

theorem wholeLifeHattendorff_countable_limit (w rho : ℕ → ℝ)
  (hw : Summable w) (hNonneg : ∀ k, 0 ≤ w k)
  (hTotal : (∑' k : ℕ, w k) = 1)
  (hS : ∀ t, 0 < wholeLifeTailMass w t)
  (hVar : Summable (fun t : ℕ =>
    (rho t) ^ 2 * w t *
      (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t))) :
  (∑' k : ℕ, w k * wholeLifeCompleteInnovation w rho k) = 0 ∧
  (∑' k : ℕ, w k * (wholeLifeCompleteInnovation w rho k) ^ 2) =
    ∑' t : ℕ, (rho t) ^ 2 * w t *
      (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t) := by sorry

end ActuarialValuation
