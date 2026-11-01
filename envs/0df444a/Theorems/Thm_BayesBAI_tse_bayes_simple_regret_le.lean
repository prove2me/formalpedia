-- Prove2me | Theorems.Thm_BayesBAI_tse_bayes_simple_regret_le
-- name    : BayesBAI.tse_bayes_simple_regret_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:00:20.551902+00:00
-- url     : https://prove2.me/theorems/53136e6d-584c-4f20-ba47-175262294ca0
-- title:
--   Theorem 1 — Bayesian simple regret of two-stage exploration is at most $C_{\mathrm{opt}}/T'+o(1/T)$
-- statement:
--   Let $K\ge2$, $q\in(0,1)$, and let $H$ be a prior on $[0,1]^K$ satisfying Assumption 1. Let $T'=2qT/K+(1-q)T$. Then the Bayesian simple regret of Algorithm 1 is bounded as
--   $$
--   \mathrm R_H(T)\le\frac{C_{\mathrm{opt}}}{T'}+o\Big(\frac1T\Big),
--   $$
--   where
--   $$
--   C_{\mathrm{opt}}=\sum_{i\in[K]}\int_{[0,1]^{K-1}}\mu^*_{\setminus i}(1-\mu^*_{\setminus i})\,h_i(\mu^*_{\setminus i}\mid\mu_{\setminus i})\,dH_{\setminus i}(\mu_{\setminus i}).
--   $$
--   The $o(1/T)$ is uniform in the tie-break rule. A leading constant of this form shows that the Bayesian simple regret decays as $1/T$, in contrast to the exponential decay of the frequentist simple regret at a fixed instance.
--
--   Differences from the source:
--   - encoding: conditional cumulative density functions of μ_i and (μ_i, μ_j) with continuous derivatives h_i, h_ij → RegularPrior: jointly measurable h, hh that disintegrate H over the laws H_\i, H_\ij by lintegral, with (4) on [0,1] and δ uniform in the conditioning vector; reason: a conditional density is this object, and C_opt does not depend on the version, since a continuous version is unique for H_\i-a.e. ν (paper.md Reading 1)
--   - encoding: Bernoulli rewards drawn adaptively → the reward tape Fin K → Fin T → Bool with independent entries; the first n pulls of an arm are its first n entries; reason: TSE fixes each stage’s pulls in advance of that stage, so the laws agree
--   - encoding: qT/K and (1−q)T/|Ĵ*| pulls, unrounded → n₁ = ⌈qT/K⌉ and n₂(s) = ⌊(T − K n₁)/s⌋; reason: pull counts are integers; the ceiling keeps Lemma 2, and with s = 2 the sample size n has |2n − T′| ≤ K + 3 (proved in a verification file) (Reading 2)
--   - generalization: arg max with ties broken arbitrarily → every TieBreak rule, with T₀ not depending on the rule; reason: specializes to any fixed rule; a randomized rule is a mixture of these (Reading 3)
--   - encoding: any q > 0, K arms → q ∈ (0,1), 2 ≤ K; reason: Algorithm 1 requires q ∈ (0,1), and μ*_\i needs a second arm (Reading 4)
--   - encoding: ≤ C_opt/T′ + o(1/T) → ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, ∀ sel, … ≤ … + ε/T; reason: o(1/T) in an upper bound means this (footnote 6, p.9); K, q, H are fixed
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Theorem 1, p.7

import Mathlib
import Definitions.Def_BayesBAI_RegularPrior
import Definitions.Def_BayesBAI_bayesSimpleRegret
import Definitions.Def_BayesBAI_Copt
import Definitions.Def_BayesBAI_tPrime

open MeasureTheory

namespace BayesBAI

/-- Theorem 1 (Bayesian simple regret upper bound of TSE), Komiyama, Ariu, Kato, Qin,
arXiv:2111.09885v3, p.7: under Assumption 1, for `q ∈ (0, 1)`, the Bayesian simple regret of Algorithm 1 is
at most `C_opt/T′ + o(1/T)`, where `T′ = 2qT/K + (1 - q)T`.

**Formalization Note.** The theorem says "any `q > 0`"; Algorithm 1 requires `q ∈ (0, 1)`. `K ≥ 2`, as
`μ*_\i` is a maximum over the other arms. `o(1/T)` in an upper bound is one-sided (footnote 6): for every
`ε > 0` the bound holds with `ε/T` for all large `T`. `T₀` does not depend on the tie-break rule, and `K`,
`q`, `H` are fixed. The theorem does not claim a matching lower bound for TSE. -/
theorem tse_bayes_simple_regret_le {K : ℕ} (hK : 2 ≤ K) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {H : Measure (Fin K → ℝ)}
    {h : (i : Fin K) → ℝ → ({j : Fin K // j ≠ i} → ℝ) → ℝ}
    {hh : (i j : Fin K) → ℝ → ℝ → ({k : Fin K // k ≠ i ∧ k ≠ j} → ℝ) → ℝ}
    (hH : RegularPrior H h hh) :
    ∀ ε > 0, ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ sel : TieBreak K,
      bayesSimpleRegret hK H sel q T ≤ Copt hK H h / tPrime K q T + ε / (T : ℝ) := by sorry

end BayesBAI
