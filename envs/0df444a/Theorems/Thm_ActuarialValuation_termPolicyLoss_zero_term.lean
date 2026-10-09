-- Prove2me | Theorems.Thm_ActuarialValuation_termPolicyLoss_zero_term
-- name    : ActuarialValuation.termPolicyLoss_zero_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:51:07.610369+00:00
-- url     : https://prove2.me/theorems/8a936f7a-a8e2-45b9-ba6b-830460cfdbe8
-- title:
--   Zero-term loss is zero regardless of premium
-- statement:
--   For n=0 neither claim nor premium payment can occur, so equivalence fails to identify a unique premium.
--
--   **Mathematical statement**
--
--   $$
--   L_0(\omega;\pi,b)=0\quad\text{for every }\pi
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_termPolicyLossPV
open MeasureTheory

namespace ActuarialValuation

theorem termPolicyLoss_zero_term {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    (b π : ℝ)
    :
    termPolicyLossPV K v 0 b π ω = 0 := by sorry

end ActuarialValuation
