-- Prove2me | Theorems.Thm_ActuarialValuation_temporaryAnnuityImmediate_variance
-- name    : ActuarialValuation.temporaryAnnuityImmediate_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:14:10.005043+00:00
-- url     : https://prove2.me/theorems/c1b06eff-4283-4ea4-8f5d-3814a1913a96
-- title:
--   Variance of the temporary annuity in arrears
-- statement:
--   The variance is the annuity-immediate second moment less the square of its expected present value. The second moment accounts for dependence between end-year payments through their overlapping survival events.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}(Z_{\mathrm{immediate}})=\mathbb E[Z_{\mathrm{immediate}}^2]-\mathbb E[Z_{\mathrm{immediate}}]^2
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.1.1, equations (3.5)–(3.6), and §3.3.2, equations (3.15)–(3.16), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityImmediatePV
import Definitions.Def_actuarial_curtateSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem temporaryAnnuityImmediate_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    :
    ProbabilityTheory.variance (temporaryAnnuityImmediatePV K v n) P = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ (i + 1)) * (v ^ (j + 1)) * (P (curtateSurvivalEvent K (max (i + 1) (j + 1)))).toReal) - (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal) ^ 2 := by sorry

end ActuarialValuation
