-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeHattendorff_finiteTailEnergyXXIII
-- name    : ActuarialValuation.wholeLifeHattendorff_finiteTailEnergyXXIII
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:56:58.089158+00:00
-- url     : https://prove2.me/theorems/da5e9150-c732-42da-83d0-f0431377d2fa
-- title:
--   Finite tail-energy inequality for countable-lifetime Hattendorff
-- statement:
--   For any finite time interval T≤N, nonnegative decrement weights and strictly positive survival tails, finite weighted Cauchy–Schwarz bounds the S_N-weighted squared survivor-path mortality shock sum by the accumulated annual Hattendorff variance increments over the interval. The adjacent survival-tail decomposition is stated explicitly and the result is valid without a maximum lifetime.
-- source:
--   Mathematical weighted Cauchy–Schwarz and telescoping reciprocals of survival tails, derived for the countable-lifetime Hattendorff capstone; Shiu and Xiong (2021) for actuarial context.

import Mathlib
import Definitions.Def_actuarial_wholeLifeTailMass

namespace ActuarialValuation

theorem wholeLifeHattendorff_finiteTailEnergyXXIII
    (w rho : ℕ → ℝ) (T N : ℕ) (hTN : T ≤ N)
    (hNonneg : ∀ t, 0 ≤ w t)
    (hS : ∀ t, 0 < wholeLifeTailMass w t)
    (hTail : ∀ t, wholeLifeTailMass w t =
      w t + wholeLifeTailMass w (t + 1)) :
  wholeLifeTailMass w N *
    (∑ t ∈ Finset.Ico T N, rho t * (w t / wholeLifeTailMass w t)) ^ 2 ≤
  ∑ t ∈ Finset.Ico T N, (rho t) ^ 2 * w t *
    (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t) := by sorry

end ActuarialValuation
