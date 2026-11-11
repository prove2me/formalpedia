-- Prove2me | Theorems.Thm_DataDepProb_Discrete_fact_4_4
-- name    : DataDepProb.Discrete.fact_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:10:27.073932+00:00
-- url     : https://prove2.me/theorems/9df9765f-557d-4c12-bc40-6e4695221454
-- title:
--   Fact 4.4 — change of measure by Cauchy–Schwarz: $|E_\mu f-E_\nu f|\le\sqrt{\chi^2(\mu\|\nu)E_\nu[f^2]}$
-- statement:
--   Let $\mu,\nu$ be probability measures on a measurable space with $\chi^2(\mu\|\nu)<\infty$, and let $f$ satisfy $E_\nu[f^2]<\infty$. Then
--   $$|E_\mu[f]-E_\nu[f]|\le\sqrt{\chi^2(\mu\|\nu)\,E_\nu[f^2]}.$$
--   If moreover $0\le f\le B$, the right-hand side is at most $\sqrt{\chi^2(\mu\|\nu)\,B\,E_\nu[f]}$. The comparison also holds after applying the same randomized procedure $K$ to both inputs: for $g$ with $E_{\nu K}[g^2]<\infty$, $|E_{\mu K}[g]-E_{\nu K}[g]|\le\sqrt{\chi^2(\mu\|\nu)E_{\nu K}[g^2]}$, and the bounded version as well.
--
--   The fact transfers expectations from an idealized experiment (fresh samples) to the amplified one; with Lemma 4.8 it is the source of the amplification error terms in the analysis.
--
--   Differences from the source:
--   - encoding: $\chi^2(\mu\|\nu)$ with "infinite divergence" for a positive numerator over a zero denominator → `chiSq μ ν : ℝ≥0∞`, equal to $\int(d\mu/d\nu-1)^2d\nu$ if $\mu\ll\nu$ and $\top$ otherwise; reason: represents the infinite case instead of a junk value.
--   - reading: $E_\nu[f^2]<\infty$ → `MemLp f 2 ν` (an a.e.-strongly measurable square-integrable $f$); reason: an expectation presupposes measurability.
--   - reading: "If $0\le f\le B$" → `∀ x, 0 ≤ f x ∧ f x ≤ B`, under the first clause's hypotheses; reason: pointwise bounds as printed.
--   - reading: "the same randomized procedure applied to both inputs" → a Markov kernel `K`, the measures `μ.bind K`, `ν.bind K`, with $\chi^2(\mu\|\nu)$ of the inputs and $g\in L^2(\nu K)$; reason: "the comparison also holds" keeps the inputs' divergence; both inequalities are restated for the outputs.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 9, Fact 4.4

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Divergence

open MeasureTheory ProbabilityTheory

namespace DataDepProb.Discrete

/-- Fact 4.4 (change of measure by Cauchy–Schwarz, p. 9). For probability measures `μ, ν` on a
measurable space and `f` with `χ²(μ‖ν) < ∞` and `E_ν[f²] < ∞` (`f ∈ L²(ν)`):
`|E_μ[f] − E_ν[f]| ≤ √(χ²(μ‖ν) E_ν[f²])`; if moreover `0 ≤ f ≤ B`, the right-hand side is at most
`√(χ²(μ‖ν) B E_ν[f])`. The same two statements hold after applying a common randomized procedure
(a Markov kernel `K`) to both inputs, with `χ²(μ‖ν)` of the inputs. -/
theorem fact_4_4 {α : Type*} [MeasurableSpace α] (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hχ : chiSq μ ν < ⊤) :
    (∀ f : α → ℝ, MemLp f 2 ν →
      |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ Real.sqrt ((chiSq μ ν).toReal * ∫ x, f x ^ 2 ∂ν) ∧
      ∀ B : ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ B) →
        Real.sqrt ((chiSq μ ν).toReal * ∫ x, f x ^ 2 ∂ν) ≤
          Real.sqrt ((chiSq μ ν).toReal * B * ∫ x, f x ∂ν)) ∧
    ∀ (β : Type*) [MeasurableSpace β] (K : Kernel α β) [IsMarkovKernel K] (g : β → ℝ),
      MemLp g 2 (ν.bind K) →
      |∫ y, g y ∂(μ.bind K) - ∫ y, g y ∂(ν.bind K)| ≤
          Real.sqrt ((chiSq μ ν).toReal * ∫ y, g y ^ 2 ∂(ν.bind K)) ∧
        ∀ B : ℝ, (∀ y, 0 ≤ g y ∧ g y ≤ B) →
          Real.sqrt ((chiSq μ ν).toReal * ∫ y, g y ^ 2 ∂(ν.bind K)) ≤
            Real.sqrt ((chiSq μ ν).toReal * B * ∫ y, g y ∂(ν.bind K)) := by sorry

end DataDepProb.Discrete
