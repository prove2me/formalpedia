-- Prove2me | Theorems.Thm_ActuarialValuation_termPolicyLossPV_integrable
-- name    : ActuarialValuation.termPolicyLossPV_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:41:02.913323+00:00
-- url     : https://prove2.me/theorems/75d6f6b6-d2f2-4874-8dab-a8a087547f1f
-- title:
--   Realised term-policy loss is integrable
-- statement:
--   Both finite present-value components are integrable, so their linear combination is integrable.
--
--   **Mathematical statement**
--
--   $$
--   L_n\in L^1(P)
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_termPolicyLossPV
open MeasureTheory

namespace ActuarialValuation

theorem termPolicyLossPV_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    (b π : ℝ)
    :
    Integrable (termPolicyLossPV K v n b π) P := by sorry

end ActuarialValuation
