-- Prove2me | Theorems.Thm_ActuarialValuation_endowment_secondMoment
-- name    : ActuarialValuation.endowment_secondMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T19:58:54.845664+00:00
-- url     : https://prove2.me/theorems/4df7a123-90c8-4560-816f-c5d0f8942135
-- title:
--   Second moment of endowment assurance
-- statement:
--   The second moment is the finite sum of squared discounted benefit amounts, each weighted by the probability of its corresponding death-year or maturity claim. These claim events are exclusive.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{endow}}^2]=\sum_{k=0}^{n-1}v^{2(k+1)}P(K=k)+v^{2n}P(K\ge n)
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.4, equation (3.10), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_endowmentAssurancePV
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deathYearEvent
open MeasureTheory

namespace ActuarialValuation

theorem endowment_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    : (∫ ω, (endowmentAssurancePV K v n ω) ^ 2 ∂P) = (∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) + (v ^ n) ^ 2 * (P (curtateSurvivalEvent K n)).toReal := by sorry

end ActuarialValuation
