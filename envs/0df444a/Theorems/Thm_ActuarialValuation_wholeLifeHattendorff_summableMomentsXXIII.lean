-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeHattendorff_summableMomentsXXIII
-- name    : ActuarialValuation.wholeLifeHattendorff_summableMomentsXXIII
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T06:44:57.682357+00:00
-- url     : https://prove2.me/theorems/b9708ba9-ea9a-422f-9641-0b9601e34df3
-- title:
--   Absolute summability of complete-life first and second Hattendorff moments
-- statement:
--   Under nonnegative unit-mass death-year weights, positive survival tails, and summable annual variance increments, a finite-prefix squared-loss telescoping identity yields absolute summability of the whole-life second moment. Weighted finite Cauchy–Schwarz then proves absolute summability of the whole-life first moment. This validates subsequent infinite-sum limit interchanges.
-- source:
--   Finite Hattendorff prefix identity and weighted Cauchy–Schwarz, derived as a genuine convergence obligation for Mission XXIII.

import Mathlib
import Definitions.Def_actuarial_wholeLifeCompleteInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

namespace ActuarialValuation

theorem wholeLifeHattendorff_summableMomentsXXIII
    (w rho : ℕ → ℝ) (hw : Summable w)
    (hNonneg : ∀ k, 0 ≤ w k)
    (hTotal : (∑' k : ℕ, w k) = 1)
    (hS : ∀ t, 0 < wholeLifeTailMass w t)
    (hVar : Summable (fun t : ℕ =>
      (rho t) ^ 2 * w t *
        (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t)))
    (hPrefix : ∀ N : ℕ,
      (∑ k ∈ Finset.range N,
        w k * (wholeLifeCompleteInnovation w rho k) ^ 2) =
      (∑ t ∈ Finset.range N,
        (rho t) ^ 2 * w t *
          (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t)) -
      wholeLifeTailMass w N *
        (-(∑ t ∈ Finset.range N,
          rho t * (w t / wholeLifeTailMass w t))) ^ 2) :
  Summable (fun k : ℕ => w k * wholeLifeCompleteInnovation w rho k) ∧
  Summable (fun k : ℕ =>
    w k * (wholeLifeCompleteInnovation w rho k) ^ 2) := by sorry

end ActuarialValuation
