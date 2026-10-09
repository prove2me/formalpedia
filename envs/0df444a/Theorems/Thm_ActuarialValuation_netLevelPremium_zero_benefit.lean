-- Prove2me | Theorems.Thm_ActuarialValuation_netLevelPremium_zero_benefit
-- name    : ActuarialValuation.netLevelPremium_zero_benefit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:50:25.314868+00:00
-- url     : https://prove2.me/theorems/ac61e40e-1888-490d-ab4d-fe599e011a53
-- title:
--   Zero sum assured gives zero net premium
-- statement:
--   Zero benefit produces zero net premium under the ratio definition, including degenerate cases.
--
--   **Mathematical statement**
--
--   $$
--   \pi^*(0)=0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_netLevelPremium
open MeasureTheory

namespace ActuarialValuation

theorem netLevelPremium_zero_benefit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    :
    netLevelPremium P K v n 0 = 0 := by sorry

end ActuarialValuation
