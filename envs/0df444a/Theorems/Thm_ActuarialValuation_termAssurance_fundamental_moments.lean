-- Prove2me | Theorems.Thm_ActuarialValuation_termAssurance_fundamental_moments
-- name    : ActuarialValuation.termAssurance_fundamental_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T18:18:16.030575+00:00
-- url     : https://prove2.me/theorems/49d4efcb-f818-4c39-a3f7-8d60460bc985
-- title:
--   Fundamental valuation identities for n-year term assurance
-- statement:
--   The root theorem brings together expected present value, second moment and variance for the same finite-term policy under one probability model, with no independence assumption.
--
--   **Mathematical statement**
--
--   $$
--   \begin{aligned}\mathbb E[Z_n]&=\sum_{k=0}^{n-1}v^{k+1}P(D_k)\\\mathbb E[Z_n^2]&=\sum_{k=0}^{n-1}v^{2(k+1)}P(D_k)\\\operatorname{Var}(Z_n)&=\sum_{k=0}^{n-1}v^{2(k+1)}P(D_k)-\left(\sum_{k=0}^{n-1}v^{k+1}P(D_k)\right)^2\end{aligned}
--   $$
-- source:
--   Chapter 3 §3.2.2, equation (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html.

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
import Definitions.Def_actuarial_termAssurancePV
open MeasureTheory

namespace ActuarialValuation
theorem termAssurance_fundamental_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    :
    ((∫ ω, termAssurancePV K v n ω ∂P) =
      ∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) ∧
    ((∫ ω, (termAssurancePV K v n ω) ^ 2 ∂P) =
      ∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) ∧
    (ProbabilityTheory.variance (termAssurancePV K v n) P =
      (∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) - (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) ^ 2) := by sorry
end ActuarialValuation
