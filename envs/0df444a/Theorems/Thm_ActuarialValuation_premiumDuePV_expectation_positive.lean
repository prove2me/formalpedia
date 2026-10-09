-- Prove2me | Theorems.Thm_ActuarialValuation_premiumDuePV_expectation_positive
-- name    : ActuarialValuation.premiumDuePV_expectation_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:40:05.204025+00:00
-- url     : https://prove2.me/theorems/4e7a8425-6308-45ce-93cf-9ea19edceabc
-- title:
--   Expected premium present value is strictly positive
-- statement:
--   The certain first instalment makes the equivalence denominator positive under a probability measure.
--
--   **Mathematical statement**
--
--   $$
--   n\ge1,\ v\ge0\Longrightarrow\mathbb E_P[Y_n]>0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
open MeasureTheory

namespace ActuarialValuation

theorem premiumDuePV_expectation_positive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    (hn : 0 < n) (hv : 0 ≤ v)
    :
    0 < ∫ ω, premiumDuePV K v n ω ∂P := by sorry

end ActuarialValuation
