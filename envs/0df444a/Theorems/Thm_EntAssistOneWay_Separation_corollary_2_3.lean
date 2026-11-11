-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_corollary_2_3
-- name    : EntAssistOneWay.Separation.corollary_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:14.683678+00:00
-- url     : https://prove2.me/theorems/25fdea05-2a26-4cda-bd90-998374b15764
-- title:
--   Corollary 2.3 — moments of independent centered Hermitian matrices
-- statement:
--   On an arbitrary probability space, let $A_1,\ldots,A_n$ be independent measurable random Hermitian $d\times d$ complex matrices with $\mathbb E A_i=0$ and $\|A_i\|_\infty\le1$ almost surely. For every even $p\ge2$,
--   $$\mathbb E\operatorname{tr}\!\left(\Bigl(\sum_i A_i\Bigr)^p\right)\le d(4pn)^{p/2}.$$
--   No finite-sample or uniform-distribution assumption is imposed. Boundedness on a probability space makes the entries and trace moment integrable. This corollary supplies a general independent-matrix estimate reusable beyond shifted equality.
--
--   Differences from the source:
--   - encoding: random matrices with E[Ai] = 0 → entrywise product measurability, iIndepFun, entrywise Bochner means, and real trace moments; reason: these express the usual finite-dimensional random-matrix conventions; boundedness implies integrability without an extra hypothesis
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 11, Corollary 2.3; pp. 11–12, proof

import Definitions.Def_EntAssistOneWay_Separation_Analysis

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Corollary 2.3, p. 11, on any probability space; expectations are entrywise. -/
theorem corollary_2_3 (Ω : Type) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n d : ℕ) (A : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeas : ∀ i, Measurable (A i))
    (hIndep : ProbabilityTheory.iIndepFun A μ)
    (hHerm : ∀ i, ∀ᵐ ω ∂μ, (A i ω).IsHermitian)
    (hBound : ∀ i, ∀ᵐ ω ∂μ, spectralNorm (A i ω) ≤ 1)
    (hMean : ∀ i a b, (∫ ω, A i ω a b ∂μ) = 0)
    (p : ℕ) (hp : Even p) (hp₂ : 2 ≤ p) :
    (∫ ω, ((∑ i, A i ω) ^ p).trace.re ∂μ) ≤
      (d : ℝ) * (4 * (p : ℝ) * n) ^ (p / 2) := by sorry

end

end EntAssistOneWay.Separation
