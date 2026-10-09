-- Prove2me | Theorems.Thm_ActuarialValuation_netLevelPremium_zero_discount
-- name    : ActuarialValuation.netLevelPremium_zero_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:51:45.666657+00:00
-- url     : https://prove2.me/theorems/69dd63f1-996e-492b-b8c3-73bb5a57c66f
-- title:
--   Zero discount factor gives zero net premium
-- statement:
--   All death benefits occur strictly after time zero while the first premium is due at inception.
--
--   **Mathematical statement**
--
--   $$
--   n\ge1,\ v=0\Longrightarrow\pi^*=0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_netLevelPremium
open MeasureTheory

namespace ActuarialValuation

theorem netLevelPremium_zero_discount {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    (b : ℝ) (hn : 0 < n)
    :
    netLevelPremium P K 0 n b = 0 := by sorry

end ActuarialValuation
