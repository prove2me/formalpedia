-- Prove2me | Theorems.Thm_ActuarialValuation_decrementCauseGain_collapse_finite
-- name    : ActuarialValuation.decrementCauseGain_collapse_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T15:59:59.903176+00:00
-- url     : https://prove2.me/theorems/0d1a0fb5-ff84-41d1-ba4f-4460143077f4
-- title:
--   Cause-aggregated mortality gain collapses to the observed cause gain minus its conditional mean
-- statement:
--   For finite competing causes, the sum of cause-specific gain coefficients times the centred death indicator is exactly the realised cause gain at death in year t less the aggregate conditional cause-weighted mean while in force. This is a pathwise identity, without independent-decrement assumptions. It is a faithful helper for the Mission XXIV Hattendorff multiple-decrement variance capstone.
-- source:
--   Gerber, Leung and Shiu (2003), Indicator Function and Hattendorff Theorem, North American Actuarial Journal 7(1), 38-47, DOI 10.1080/10920277.2003.10596075; Actuarial Mathematics XXIV, 9e01c12a-3020-4102-8cfc-c3f8ce9672cd

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation
import Definitions.Def_actuarial_decrementTailMass

theorem ActuarialValuation.decrementCauseGain_collapse_finite
    {C : Type*} [Fintype C] (w rho : ℕ → C → ℝ)
    (t k : ℕ) (d : C) :
    (∑ c : C, rho t c * ActuarialValuation.decrementCauseInnovation w t c k d) =
    (if k = t then rho t d else 0) -
      ((∑ c : C, w t c * rho t c) /
        ActuarialValuation.decrementTailMass w t) *
        (if t ≤ k then (1 : ℝ) else 0) := by sorry
