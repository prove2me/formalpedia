-- Prove2me | Theorems.Thm_BayesBAI_lemma_14
-- name    : BayesBAI.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:56:46.794109+00:00
-- url     : https://prove2.me/theorems/a3362fed-b005-469b-ad51-f655cd37843a
-- title:
--   Lemma 14 — tight Bayesian bound (corrected: $\mu_j\ge T^{-1/6}$, $m$ read as $\mu_j$, without $\mathcal S$)
-- statement:
--   Let $n=n_1+n_2(2)$. For every $\epsilon>0$ there is $T_0$ such that for all $T\ge T_0$, all $\mu\in[0,1]^K$ and all arms $i\ne j$ with $T^{-1/6}\le\mu_j<1-T^{-1/6}$,
--   $$
--   \int_{\mu_j}^{\min(\mu_j+2B_{\mathrm{conf}},\,1-T^{-1/6})}(x-\mu_j)\,\mathbb P_{\mu[i\mapsto x]}[\hat\mu_{i,n}\le\hat\mu_{j,n}]\,dx\le(1+\epsilon)\frac{\mu_j(1-\mu_j)}{T'},
--   $$
--   where $\mu[i\mapsto x]$ is $\mu$ with coordinate $i$ replaced by $x$. The threshold $T_0$ does not depend on the means.
--
--   Integrating this against the prior gives the constant $C_{\mathrm{opt}}$ in Lemma 4.
--
--   Differences from the source:
--   - reading: m(1−m)/T′ with m = (μ_i + μ_j)/2 on the right side, after μ_i is integrated out → μ_j(1−μ_j)/T′; reason: the proof of Lemma 4 applies it with μ_j, and μ_i is bound on the left side (Reading 5)
--   - correction: no lower bound on μ_j, and the event {μ̂_i ≤ μ̂_j, S} → T^(−1/6) ≤ μ_j, and the event {μ̂_i ≤ μ̂_j} without S; reason: false at μ_j = 1/T², where the left side has order 1/T² and the right side 1/T³; dropping S enlarges the event, so it implies the printed bound on the corrected range (Reading 5)
--   - generalization: (1 + o(1)), with no statement on how the o(1) depends on μ → ∃ T₀ before μ, i, j: the bound is uniform in the means; reason: the uniform statement specializes to each fixed μ, and Lemma 4 integrates it over the prior, which needs uniformity
--   - encoding: T′_h = T′/2 samples → n = n₁ + n₂(2) samples, with T′ real in the right side; reason: the sample size is an integer (Reading 2)
--   - encoding: the integral over μ_i, with upper limit min(μ_j + 2B_conf, 1 − T^(−1/6)) and μ_j unconstrained above → the interval integral in x of tapePr (Function.update μ i x), with μ_j < 1 − T^(−1/6); reason: the same integral, with the range nonempty; the probability is a polynomial in x
--   - encoding: Bernoulli rewards drawn adaptively → the reward tape Fin K → Fin T → Bool with independent entries; the first n pulls of an arm are its first n entries; reason: TSE fixes each stage’s pulls in advance of that stage, so the laws agree
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Lemma 14, p.20

import Mathlib
import Definitions.Def_BayesBAI_Bconf
import Definitions.Def_BayesBAI_empMean
import Definitions.Def_BayesBAI_secondPulls
import Definitions.Def_BayesBAI_tPrime
import Definitions.Def_BayesBAI_tapePr

namespace BayesBAI

/-- Lemma 14 (tight Bayesian bound), Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.20, corrected:
with `n = n₁ + n₂(2)`, for `T` large, uniformly in the means, if `T^(-1/6) ≤ μ_j < 1 - T^(-1/6)`, then
`∫_{μ_j}^{min(μ_j + 2 B_conf, 1 - T^(-1/6))} (x - μ_j) ℙ_{μ[i ↦ x]}[μ̂_{i,n} ≤ μ̂_{j,n}] dx ≤ (1 + ε) μ_j(1 - μ_j)/T′`.

**Formalization Note.** The page has `m(1 - m)` on the right side with `m = (μ_i + μ_j)/2`, after `μ_i`
has been integrated out, and the proof of Lemma 4 applies it with `μ_j`: this is the reading. As
printed there is no lower bound on `μ_j`, and the claim fails at `μ_j = 1/T²`, where the left side is of
order `1/T²` and the right side of order `1/T³`. The corrections are `T^(-1/6) ≤ μ_j` and no `𝒮`.
`T₀` is chosen before the means. The integrand is a polynomial in `x`, so the interval integral is
genuine. -/
theorem lemma_14 {K : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∀ ε > 0, ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ (μ : Fin K → ℝ), (∀ k, μ k ∈ Set.Icc (0 : ℝ) 1) →
      ∀ i j : Fin K, i ≠ j →
      (T : ℝ) ^ (-(1 / 6) : ℝ) ≤ μ j → μ j < 1 - (T : ℝ) ^ (-(1 / 6) : ℝ) →
      let n := firstPulls K q T + secondPulls K q T 2
      ∫ x in (μ j)..(min (μ j + 2 * Bconf K q T) (1 - (T : ℝ) ^ (-(1 / 6) : ℝ))),
        (x - μ j) * tapePr (Function.update μ i x)
          {ω : Tape K T | empMean ω i n ≤ empMean ω j n} ≤
        (1 + ε) * (μ j * (1 - μ j)) / tPrime K q T := by sorry

end BayesBAI
