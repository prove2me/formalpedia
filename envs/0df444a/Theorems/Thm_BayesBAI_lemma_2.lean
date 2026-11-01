-- Prove2me | Theorems.Thm_BayesBAI_lemma_2
-- name    : BayesBAI.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:57:03.468289+00:00
-- url     : https://prove2.me/theorems/d9382743-cbaa-4200-a945-de7263df2d22
-- title:
--   Lemma 2 — $\mathcal S$ occurs with high probability
-- statement:
--   For all means $\mu\in[0,1]^K$ and all $T\ge1$,
--   $$
--   \mathbb P[\mathcal S]\ge1-\frac{2K}{T^2}.
--   $$
--   So the true means lie in all the confidence intervals, up to an event of negligible weight in the regret.
--
--   Differences from the source:
--   - encoding: Bernoulli rewards drawn adaptively → the reward tape Fin K → Fin T → Bool with independent entries; the first n pulls of an arm are its first n entries; reason: TSE fixes each stage’s pulls in advance of that stage, so the laws agree
--   - encoding: qT/K and (1−q)T/|Ĵ*| pulls, unrounded → n₁ = ⌈qT/K⌉ and n₂(s) = ⌊(T − K n₁)/s⌋; reason: pull counts are integers; the ceiling keeps Lemma 2, and with s = 2 the sample size n has |2n − T′| ≤ K + 3 (proved in a verification file) (Reading 2)
--   - encoding: any q > 0, K arms → q ∈ (0,1), 2 ≤ K; reason: Algorithm 1 requires q ∈ (0,1), and μ*_\i needs a second arm (Reading 4)
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Lemma 2, p.7

import Mathlib
import Definitions.Def_BayesBAI_goodEvent
import Definitions.Def_BayesBAI_tapePr

namespace BayesBAI

/-- Lemma 2 (`𝒮` occurs with high probability), Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.7:
`ℙ[𝒮] ≥ 1 - 2K/T²`, for all means in the cube and all `T ≥ 1`. -/
theorem lemma_2 {K : ℕ} (hK : 2 ≤ K) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {T : ℕ} (hT : 1 ≤ T)
    {μ : Fin K → ℝ} (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1) :
    tapePr μ {ω : Tape K T | goodEvent q μ ω} ≥ 1 - 2 * (K : ℝ) / (T : ℝ) ^ 2 := by sorry

end BayesBAI
