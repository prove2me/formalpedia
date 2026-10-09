-- Prove2me | Theorems.Thm_ActuarialValuation_endowment_expectation
-- name    : ActuarialValuation.endowment_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T19:58:05.184974+00:00
-- url     : https://prove2.me/theorems/2d8b6d8b-614c-478c-b594-5f0e4bf1f1b4
-- title:
--   Expected present value of endowment assurance
-- statement:
--   The expected present value is the finite sum of discounted probabilities of death in each covered year, together with the maturity discount factor times the probability that curtate lifetime is at least the term.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{endow}}]=\sum_{k=0}^{n-1}v^{k+1}P(K=k)+v^nP(K\ge n)
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.4, equation (3.10), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_endowmentAssurancePV
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deathYearEvent
open MeasureTheory

namespace ActuarialValuation

theorem endowment_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    : (∫ ω, endowmentAssurancePV K v n ω ∂P) = (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) + v ^ n * (P (curtateSurvivalEvent K n)).toReal := by sorry

end ActuarialValuation
