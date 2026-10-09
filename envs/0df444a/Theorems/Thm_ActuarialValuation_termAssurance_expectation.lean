-- Prove2me | Theorems.Thm_ActuarialValuation_termAssurance_expectation
-- name    : ActuarialValuation.termAssurance_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T18:15:35.731982+00:00
-- url     : https://prove2.me/theorems/7ea6e1ce-b75d-48f7-b416-1384b00b6f1c
-- title:
--   Expected present value of an n-year term assurance
-- statement:
--   Establish that expected present value sums, over covered years, each end-of-year discount multiplied by that year’s death probability.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_n]=\sum_{k=0}^{n-1}v^{k+1}P(D_k)
--   $$
-- source:
--   Chapter 3 §3.2.2, equation (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html.

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
import Definitions.Def_actuarial_termAssurancePV
open MeasureTheory

namespace ActuarialValuation
theorem termAssurance_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    :
    (∫ ω, termAssurancePV K v n ω ∂P) =
      ∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal := by sorry
end ActuarialValuation
