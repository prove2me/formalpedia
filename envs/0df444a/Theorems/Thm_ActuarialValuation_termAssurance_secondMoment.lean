-- Prove2me | Theorems.Thm_ActuarialValuation_termAssurance_secondMoment
-- name    : ActuarialValuation.termAssurance_secondMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T18:16:59.984751+00:00
-- url     : https://prove2.me/theorems/4b7f0aa3-d366-48c6-a2f2-9befc5365f07
-- title:
--   Second moment of an n-year term assurance
-- statement:
--   Derive the second moment and show that the single possible death benefit leaves no cross-products between distinct death years.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_n^2]=\sum_{k=0}^{n-1}v^{2(k+1)}P(D_k)
--   $$
-- source:
--   Chapter 3 §3.2.2, equation (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html.

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
import Definitions.Def_actuarial_termAssurancePV
open MeasureTheory

namespace ActuarialValuation
theorem termAssurance_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    :
    (∫ ω, (termAssurancePV K v n ω) ^ 2 ∂P) =
      ∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal := by sorry
end ActuarialValuation
