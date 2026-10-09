-- Prove2me | Theorems.Thm_ActuarialValuation_netLevelPremium_equivalence
-- name    : ActuarialValuation.netLevelPremium_equivalence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:46:59.20361+00:00
-- url     : https://prove2.me/theorems/1e19bd90-144c-4bb4-855c-042f81458713
-- title:
--   Net premium satisfies the equivalence principle
-- statement:
--   The defined net premium makes expected loss at issue zero when the premium-annuity EPV is positive.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_P[L_n(\pi^*,b)]=0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_termPolicyLossPV
import Definitions.Def_actuarial_netLevelPremium
open MeasureTheory

namespace ActuarialValuation

theorem netLevelPremium_equivalence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    (b : ℝ) (hn : 0 < n) (hv : 0 ≤ v)
    :
    (∫ ω, termPolicyLossPV K v n b (netLevelPremium P K v n b) ω ∂P) = 0 := by sorry

end ActuarialValuation
