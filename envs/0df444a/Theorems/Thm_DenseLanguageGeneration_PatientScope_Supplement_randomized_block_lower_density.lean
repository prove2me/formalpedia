-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_Supplement_randomized_block_lower_density
-- name    : DenseLanguageGeneration.PatientScope.Supplement.randomized_block_lower_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:01:51.517596+00:00
-- url     : https://prove2.me/theorems/8f37ad30-d0c5-4a67-9a55-5e758b2a5982
-- title:
--   Theorem 4.3 — Fixed-block randomized bound and its limit
-- statement:
--   Define $f(q)=1-(1-1/(q+1))^q$. For every positive integer $m$ and every known countably indexed family $\mathcal L$ of infinite languages, there is a randomized causal generator $R$ such that for every target $K=L_i$ and every full enumeration $a$ fixed independently of its randomness,
--
--   $$\underline d_R(K,a)\ge\left(1-\frac1{m+1}\right)f(m+1).$$
--
--   The explicit guarantees satisfy the additional conclusion
--
--   $$\lim_{m\to\infty}\left(1-\frac1{m+1}\right)f(m+1)=1-e^{-1}.$$
--
--   The statistic $\underline d_R$ is the liminf of expected owned-prefix counts divided by the target-prefix count. One algorithm is chosen before the target and enumeration, but may depend on $m$ and the family. This companion theorem retains both the finite-parameter bound and its limiting value; in particular, $f$ is evaluated at $m+1$.
--
--   Differences from the source:
--   - encoding: positive family indices and rounds → zero-based Family and stream indices; the response at index t sees inputs 0 through t; reason: adding one identifies the indices, and causal replay also recovers the generator's own past outputs
--   - encoding: a randomized algorithm against a non-adaptive adversary → a probability space with measurable random history responses and an enumeration fixed outside the expectation; reason: presampling the private randomness represents every causal randomized strategy; countable discrete outputs require exactly measurable singleton fibres
--   - encoding: prefix-count ratios and their asymptotic lower limits → real ratios with zero at a zero denominator and Filter.liminf atTop; reason: all numerators are measurable finite counts bounded by the corresponding denominator; an infinite target has eventually positive denominators, so the total convention changes no lower density
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), Theorem 4.3, printed pp.18–19 (PDF pp.20–21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_randomized

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy
open DenseLanguageGeneration.PatientScope
open Filter Topology

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- Cai et al., STOC 2027 submission #335 (October 2026), Theorem 4.3,
printed pp.18–19 (PDF pp.20–21); proof printed pp.19–25 (PDF pp.21–27).
The bound is (1 − 1/(m+1))·f(m+1) with f = rankingRatio evaluated at m+1, and the
second sentence of the theorem is the limit conjunct. -/
theorem randomized_block_lower_density :
    (∀ m : ℕ, 1 ≤ m → ∀ L : Family, ∃ R : RandomizedGenerator,
      ∀ (i : ℕ) (a : ℕ → ℕ+), IsEnumeration (L i) a →
        (1 - 1 / ((m : ℝ) + 1)) * rankingRatio (m + 1) ≤ randomizedLowerDensity R (L i) a) ∧
    Tendsto (fun m : ℕ => (1 - 1 / ((m : ℝ) + 1)) * rankingRatio (m + 1)) atTop
      (𝓝 (1 - Real.exp (-1))) := by sorry

end DenseLanguageGeneration.PatientScope.Supplement
