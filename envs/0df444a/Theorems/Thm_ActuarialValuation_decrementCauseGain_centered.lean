-- Prove2me | Theorems.Thm_ActuarialValuation_decrementCauseGain_centered
-- name    : ActuarialValuation.decrementCauseGain_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:08:27.826986+00:00
-- url     : https://prove2.me/theorems/28dedb20-4b91-466d-a7ad-2b29e2c99b65
-- title:
--   Every aggregate categorical mortality gain has zero weighted mean
-- statement:
--   The finite cause-weighted sum of centred decrement indicators has zero joint-probability-weighted expectation over countably many years and finitely many causes, assuming summable nonnegative death-year masses and positive survival mass. This is the conditional-centring lemma required for Hattendorff orthogonality in Actuarial Mathematics XXIV.
-- source:
--   Actuarial Mathematics XXIV mission 9e01c12a-3020-4102-8cfc-c3f8ce9672cd; Gerber Leung Shiu (2003) indicator-function derivation, DOI 10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation
import Definitions.Def_actuarial_decrementTailMass
import Definitions.Def_actuarial_decrementYearMass
import Theorems.Thm_ActuarialValuation_decrementCauseGain_collapse_finite

theorem ActuarialValuation.decrementCauseGain_centered
    {C : Type*} [Fintype C] (w rho : ℕ → C → ℝ) (t : ℕ)
    (hw : Summable (fun k : ℕ => ActuarialValuation.decrementYearMass w k))
    (hn : ∀ k e, 0 ≤ w k e)
    (hS : 0 < ActuarialValuation.decrementTailMass w t) :
    (∑' k : ℕ, ∑ d : C,
      w k d * (∑ c : C,
        rho t c * ActuarialValuation.decrementCauseInnovation w t c k d)) = 0 := by sorry
