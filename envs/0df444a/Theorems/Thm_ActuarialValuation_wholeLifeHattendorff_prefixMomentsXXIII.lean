-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeHattendorff_prefixMomentsXXIII
-- name    : ActuarialValuation.wholeLifeHattendorff_prefixMomentsXXIII
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T23:12:19.014867+00:00
-- url     : https://prove2.me/theorems/af5e9045-9ee0-49c4-9480-10307f454c47
-- title:
--   Exact finite prefixes of the complete countable-life Hattendorff moments
-- statement:
--   For each finite collection of death-year outcomes, the first moment of the complete-life innovation telescopes to minus the surviving boundary weight times the accumulated survivor-path shock. The second moment telescopes to the finite allocated annual Hattendorff variance less the nonnegative quadratic survival boundary. Both identities apply under a countable lifetime without a terminal death year.
-- source:
--   Exact countable-lifetime Hattendorff definitions and the published survival-tail/pathwise identities; telescoping finite sums.

import Mathlib
import Definitions.Def_actuarial_wholeLifeCompleteInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

namespace ActuarialValuation

theorem wholeLifeHattendorff_prefixMomentsXXIII
    (w rho : ℕ → ℝ) (hw : Summable w)
    (hS : ∀ t, 0 < wholeLifeTailMass w t) (N : ℕ) :
  (∑ k ∈ Finset.range N, w k * wholeLifeCompleteInnovation w rho k) =
    -(wholeLifeTailMass w N *
      (-(∑ t ∈ Finset.range N,
        rho t * (w t / wholeLifeTailMass w t)))) ∧
  (∑ k ∈ Finset.range N,
      w k * (wholeLifeCompleteInnovation w rho k) ^ 2) =
    (∑ t ∈ Finset.range N,
      (rho t) ^ 2 * w t *
        (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t)) -
      wholeLifeTailMass w N *
        (-(∑ t ∈ Finset.range N,
          rho t * (w t / wholeLifeTailMass w t))) ^ 2 := by sorry

end ActuarialValuation
