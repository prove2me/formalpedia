-- Prove2me | Theorems.Thm_ActuarialValuation_endowment_variance
-- name    : ActuarialValuation.endowment_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T19:59:30.433929+00:00
-- url     : https://prove2.me/theorems/e02c06a4-84cc-4fff-b8f7-9f7ed8cb3cfe
-- title:
--   Variance of endowment assurance
-- statement:
--   The variance of the endowment present value is its second moment less the square of its expected present value.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{endow}}^2]=\sum_{k=0}^{n-1}v^{2(k+1)}P(K=k)+v^{2n}P(K\ge n)-\left(\mathbb E[Z_{\mathrm{endow}}]\right)^2
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.4, equation (3.10), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_endowmentAssurancePV
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deathYearEvent
open MeasureTheory

namespace ActuarialValuation

theorem endowment_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    : ProbabilityTheory.variance (endowmentAssurancePV K v n) P = ((∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) + (v ^ n) ^ 2 * (P (curtateSurvivalEvent K n)).toReal) - ((∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) + v ^ n * (P (curtateSurvivalEvent K n)).toReal) ^ 2 := by sorry

end ActuarialValuation
