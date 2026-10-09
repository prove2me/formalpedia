-- Prove2me | Theorems.Thm_ActuarialValuation_netLevelPremium_benefit_scale
-- name    : ActuarialValuation.netLevelPremium_benefit_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:48:32.221241+00:00
-- url     : https://prove2.me/theorems/4d662abd-cdfc-4943-9f40-0f5d164c4a27
-- title:
--   Net premium scales with sum assured
-- statement:
--   Multiplying all claim benefits by a constant multiplies the net premium by that constant.
--
--   **Mathematical statement**
--
--   $$
--   \pi^*(cb)=c\pi^*(b)
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_netLevelPremium
open MeasureTheory

namespace ActuarialValuation

theorem netLevelPremium_benefit_scale {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    (b c : ℝ)
    :
    netLevelPremium P K v n (c * b) = c * netLevelPremium P K v n b := by sorry

end ActuarialValuation
