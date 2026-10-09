-- Prove2me | Theorems.Thm_ActuarialValuation_termAssurance_variance
-- name    : ActuarialValuation.termAssurance_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T18:17:26.203212+00:00
-- url     : https://prove2.me/theorems/f9a1397f-edd6-41f4-97d3-9b9099e6e471
-- title:
--   Variance of an n-year term assurance
-- statement:
--   Establish that variance equals the discounted second-moment sum minus the square of expected present value.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}(Z_n)=\sum_{k=0}^{n-1}v^{2(k+1)}P(D_k)-\left(\sum_{k=0}^{n-1}v^{k+1}P(D_k)\right)^2
--   $$
-- source:
--   Chapter 3 §3.2.2, equation (3.8) and §3.1.1 (3.4), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html.

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
import Definitions.Def_actuarial_termAssurancePV
open MeasureTheory

namespace ActuarialValuation
theorem termAssurance_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    :
    ProbabilityTheory.variance (termAssurancePV K v n) P =
      (∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) - (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) ^ 2 := by sorry
end ActuarialValuation
