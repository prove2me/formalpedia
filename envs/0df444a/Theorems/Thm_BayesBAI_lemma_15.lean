-- Prove2me | Theorems.Thm_BayesBAI_lemma_15
-- name    : BayesBAI.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:56:32.148289+00:00
-- url     : https://prove2.me/theorems/b6a27572-3052-4dcd-92c3-52cd87c0d849
-- title:
--   Lemma 15 — tight frequentist bound (corrected: $\mu_j\ge T^{-1/6}$, without $\mathcal S$)
-- statement:
--   Let $n=n_1+n_2(2)$, the sample size of each candidate when there are two. For every $\epsilon>0$ there is $T_0$ such that for all $T\ge T_0$, all $\mu\in[0,1]^K$ and all arms $i\ne j$ with
--   $$
--   T^{-1/6}\le\mu_j<\mu_i<\min(\mu_j+2B_{\mathrm{conf}},\,1-T^{-1/6}),
--   $$
--   writing $m=(\mu_i+\mu_j)/2$ and $\Delta=\mu_i-\mu_j$,
--   $$
--   (1-\epsilon)\,G\le\mathbb P_\mu[\hat\mu_{i,n}\le\hat\mu_{j,n}]\le(1+\epsilon)\,G,\qquad G=\sqrt{\frac{T'}{8\pi m(1-m)}}\int_0^\infty e^{-\frac{T'}{8m(1-m)}(\Delta^2+2s_2\Delta+s_2^2)}\,ds_2,
--   $$
--   that is, $\mathbb P_\mu[\hat\mu_{i,n}\le\hat\mu_{j,n}]=(1+o(1))\,G$. The threshold $T_0$ does not depend on the means. The right side is the Gaussian tail with the exact variance, which is what gives the sharp constant of Theorem 1; a Chernoff bound would lose a factor.
--
--   Differences from the source:
--   - correction: μ*_\ij < μ_j < μ_i < min(μ_j + 2B_conf, 1 − T^(−1/6)), no lower bound on μ_j → T^(−1/6) ≤ μ_j < μ_i < min(…); reason: false at small means: K = 3, q = 1/2, μ_k = 0, μ_j = 1/T², μ_i = 1/T satisfy the printed hypotheses, with left side → 0.659 and right side → 0.259 (Reading 6)
--   - correction: ℙ_μ[μ̂_{i,T′_h} ≤ μ̂_{j,T′_h}, S] = (1+o(1)) · Gaussian expression → (1−ε) · Gaussian expression ≤ ℙ_μ[μ̂_{i,n} ≤ μ̂_{j,n}] ≤ (1+ε) · Gaussian expression, with no S; reason: near gap 2B_conf, conditioning on the error tilts the first-stage means onto the boundary of S, and P[A, S]/P[A] is about 0.19 by exact sums at gap 1.998 B_conf, K = 2, q = 1/2, T = 2000 to 32000, so the equality with S fails; the two-sided 1 + o(1) of the page is kept for the event without S, and its upper half implies the ≤ half of the printed form (Reading 6)
--   - generalization: hypothesis μ*_\ij < μ_j → dropped; reason: the claim concerns arms i, j only, so it specializes to the hypothesis
--   - encoding: T′_h = T′/2 samples → n = n₁ + n₂(2) samples, with T′ real in the right side; reason: the sample size is an integer, and |2n − T′| ≤ K + 3 is absorbed by the 1 + ε (Reading 2)
--   - encoding: Bernoulli rewards drawn adaptively → the reward tape Fin K → Fin T → Bool with independent entries; the first n pulls of an arm are its first n entries; reason: TSE fixes each stage’s pulls in advance of that stage, so the laws agree
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Lemma 15, pp.20–21

import Mathlib
import Definitions.Def_BayesBAI_Bconf
import Definitions.Def_BayesBAI_empMean
import Definitions.Def_BayesBAI_secondPulls
import Definitions.Def_BayesBAI_tPrime
import Definitions.Def_BayesBAI_tapePr

open MeasureTheory

namespace BayesBAI

/-- Lemma 15 (tight frequentist bound), Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, pp.20–21,
corrected: with `n = n₁ + n₂(2)` the sample size of each of two candidates, for `T` large, uniformly in
the means, if `T^(-1/6) ≤ μ_j < μ_i < min(μ_j + 2 B_conf, 1 - T^(-1/6))`, then with `m = (μ_i + μ_j)/2`
and `Δ = μ_i - μ_j`,
`ℙ_μ[μ̂_{i,n} ≤ μ̂_{j,n}] = (1 + o(1)) G`, i.e. `(1 - ε) G ≤ ℙ_μ[μ̂_{i,n} ≤ μ̂_{j,n}] ≤ (1 + ε) G`, where
`G = √(T′/(8π m(1 - m))) ∫_{s > 0} exp(-(T′/(8m(1 - m)))(Δ² + 2sΔ + s²)) ds`.

**Formalization Note.** The printed lemma is an equality for `ℙ_μ[μ̂_{i,T′_h} ≤ μ̂_{j,T′_h}, 𝒮]` under
`μ*_\ij < μ_j < μ_i < min(⋯)`. As printed it fails: `K = 3`, `q = 1/2`, `μ_k = 0`, `μ_j = 1/T²`, `μ_i = 1/T` has
left side `≈ 0.659` and right side `≈ 0.259`; and near gap `2 B_conf`, `ℙ[A, 𝒮]` is about `ℙ[A]/4`. The
corrections are the lower bound `T^(-1/6) ≤ μ_j` and no `𝒮`; the two-sided `1 + o(1)` of the page is
kept. The condition `μ*_\ij < μ_j` is dropped, since the claim concerns two arms only. `T′_h = T′/2` is rounded to the integer `n`;
`T′` stays real, and `|2n - T′| ≤ K + 3`. The Gaussian integrand is integrable, as `T′ > 0` and
`0 < m < 1`. `T₀` is chosen before the means: the `o(1)` does not depend on them. -/
theorem lemma_15 {K : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∀ ε > 0, ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ (μ : Fin K → ℝ), (∀ k, μ k ∈ Set.Icc (0 : ℝ) 1) →
      ∀ i j : Fin K, i ≠ j →
      (T : ℝ) ^ (-(1 / 6) : ℝ) ≤ μ j → μ j < μ i →
      μ i < min (μ j + 2 * Bconf K q T) (1 - (T : ℝ) ^ (-(1 / 6) : ℝ)) →
      let n := firstPulls K q T + secondPulls K q T 2
      let m := (μ i + μ j) / 2
      let Δ := μ i - μ j
      let G := Real.sqrt (tPrime K q T / (8 * Real.pi * m * (1 - m))) *
        ∫ s in Set.Ioi (0 : ℝ),
          Real.exp (-(tPrime K q T / (8 * m * (1 - m))) * (Δ ^ 2 + 2 * s * Δ + s ^ 2))
      (1 - ε) * G ≤ tapePr μ {ω : Tape K T | empMean ω i n ≤ empMean ω j n} ∧
        tapePr μ {ω : Tape K T | empMean ω i n ≤ empMean ω j n} ≤ (1 + ε) * G := by sorry

end BayesBAI
