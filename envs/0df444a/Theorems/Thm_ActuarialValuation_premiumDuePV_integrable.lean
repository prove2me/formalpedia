-- Prove2me | Theorems.Thm_ActuarialValuation_premiumDuePV_integrable
-- name    : ActuarialValuation.premiumDuePV_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:37:53.905834+00:00
-- url     : https://prove2.me/theorems/2da5ff5a-9cf5-4271-aa95-6a31b640eef0
-- title:
--   Finite premium present value is integrable
-- statement:
--   A finite sum of bounded measurable survival-contingent instalments is integrable at any real discount factor.
--
--   **Mathematical statement**
--
--   $$
--   Y_n\in L^1(P)
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
open MeasureTheory

namespace ActuarialValuation

theorem premiumDuePV_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    :
    Integrable (premiumDuePV K v n) P := by sorry

end ActuarialValuation
