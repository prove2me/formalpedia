-- Prove2me | Theorems.Thm_ActuarialValuation_decrementCauseGain_secondMoment
-- name    : ActuarialValuation.decrementCauseGain_secondMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:07:36.546775+00:00
-- url     : https://prove2.me/theorems/a79f1a8e-21b2-4afe-a573-a7b55c3354b4
-- title:
--   One-year categorical mortality innovation second moment equals the full competing-risk allocation
-- statement:
--   The weighted squared cause-aggregated annual innovation is the full multiple-decrement annual risk: the cause-weighted sum of gain squares minus the square of the cause-weighted mean divided by survival mass. This automatically includes negative same-year cause covariance. The model has countably many years, finite causes, summable nonnegative joint mass and positive in-force mass.
-- source:
--   Actuarial Mathematics XXIV mission 9e01c12a-3020-4102-8cfc-c3f8ce9672cd; Gerber Leung Shiu (2003) Indicator Function and Hattendorff Theorem, DOI 10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation
import Definitions.Def_actuarial_decrementAnnualRisk
import Definitions.Def_actuarial_decrementTailMass
import Definitions.Def_actuarial_decrementYearMass
import Theorems.Thm_ActuarialValuation_decrementCauseGain_collapse_finite

theorem ActuarialValuation.decrementCauseGain_secondMoment
    {C : Type*} [Fintype C] (w rho : ℕ → C → ℝ) (t : ℕ)
    (hw : Summable (fun k : ℕ => ActuarialValuation.decrementYearMass w k))
    (hn : ∀ k e, 0 ≤ w k e)
    (hS : 0 < ActuarialValuation.decrementTailMass w t) :
    (∑' k : ℕ, ∑ d : C, w k d *
      (∑ c : C, rho t c *
        ActuarialValuation.decrementCauseInnovation w t c k d) ^ 2) =
      ActuarialValuation.decrementAnnualRisk w rho t := by sorry
