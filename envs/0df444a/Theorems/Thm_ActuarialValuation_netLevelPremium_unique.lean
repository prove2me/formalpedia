-- Prove2me | Theorems.Thm_ActuarialValuation_netLevelPremium_unique
-- name    : ActuarialValuation.netLevelPremium_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:47:42.75577+00:00
-- url     : https://prove2.me/theorems/940bbd7f-d541-4fde-9c63-ead516bc1964
-- title:
--   Equivalence net premium is unique
-- statement:
--   A strictly positive denominator rules out a second level premium with zero expected loss.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_P[L_n(\pi,b)]=0\Longrightarrow \pi=\pi^*
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_termPolicyLossPV
import Definitions.Def_actuarial_netLevelPremium
open MeasureTheory

namespace ActuarialValuation

theorem netLevelPremium_unique {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    (b π : ℝ) (hn : 0 < n) (hv : 0 ≤ v)
    (hzero : (∫ ω, termPolicyLossPV K v n b π ω ∂P) = 0)
    :
    π = netLevelPremium P K v n b := by sorry

end ActuarialValuation
