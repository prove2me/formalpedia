-- Prove2me | Theorems.Thm_ActuarialValuation_netLevelPremium_fundamental_equivalence
-- name    : ActuarialValuation.netLevelPremium_fundamental_equivalence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:52:33.063146+00:00
-- url     : https://prove2.me/theorems/5bf1559e-9618-4e83-bff0-f917aec8778e
-- title:
--   Fundamental valuation and uniqueness of the net level premium
-- statement:
--   Combines positive premium annuity EPV, zero expected loss at the quoted net premium, uniqueness and benefit scaling.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_P[Y_n]>0,\quad \mathbb E_P[L_n(\pi^*,b)]=0,\quad\pi^*\text{ unique}
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
import Definitions.Def_actuarial_termPolicyLossPV
import Definitions.Def_actuarial_netLevelPremium
open MeasureTheory

namespace ActuarialValuation

theorem netLevelPremium_fundamental_equivalence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    (b c : ℝ) (hn : 0 < n) (hv : 0 ≤ v)
    :
    (0 < ∫ ω, premiumDuePV K v n ω ∂P)
    ∧ ((∫ ω, termPolicyLossPV K v n b
          (netLevelPremium P K v n b) ω ∂P) = 0)
    ∧ (∀ π : ℝ, (∫ ω, termPolicyLossPV K v n b π ω ∂P) = 0 →
          π = netLevelPremium P K v n b)
    ∧ (netLevelPremium P K v n (c * b) =
          c * netLevelPremium P K v n b) := by sorry

end ActuarialValuation
