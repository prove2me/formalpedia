-- Prove2me | Theorems.Thm_ActuarialValuation_termPolicyLoss_expected_linear
-- name    : ActuarialValuation.termPolicyLoss_expected_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:44:03.508736+00:00
-- url     : https://prove2.me/theorems/c9fa7ed6-1345-46e0-af6c-d060624fd134
-- title:
--   Expected loss splits into claim and premium values
-- statement:
--   Linearity of expectation gives the loss-at-issue equation without independence assumptions.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_P[L_n]=b\,\mathbb E_P[A_n]-\pi\,\mathbb E_P[Y_n]
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
import Definitions.Def_actuarial_termPolicyLossPV
open MeasureTheory

namespace ActuarialValuation

theorem termPolicyLoss_expected_linear {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    (b π : ℝ)
    :
    (∫ ω, termPolicyLossPV K v n b π ω ∂P) =
      b * (∫ ω, termAssurancePV K v n ω ∂P) -
      π * (∫ ω, premiumDuePV K v n ω ∂P) := by sorry

end ActuarialValuation
