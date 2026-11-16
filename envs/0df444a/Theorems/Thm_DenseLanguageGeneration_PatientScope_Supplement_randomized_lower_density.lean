-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_Supplement_randomized_lower_density
-- name    : DenseLanguageGeneration.PatientScope.Supplement.randomized_lower_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:01:07.168427+00:00
-- url     : https://prove2.me/theorems/1b828566-fb18-49e0-8527-9119a501055d
-- title:
--   Theorem 4.2 — Randomized lower density
-- statement:
--   For every known countably indexed family $\mathcal L=(L_1,L_2,\ldots)$ of infinite subsets of $\mathbb Z_{>0}$, there is a randomized causal generator $R$, chosen from the family alone, such that for every target $K=L_i$ and every full injective enumeration $a$ of $K$ fixed independently of the private randomness,
--
--   $$\liminf_{n\to\infty}\frac{\mathbb E_\omega[|D_\omega\cap K\cap[n]|]}{|K\cap[n]|}\ge1-e^{-1}.$$
--
--   Here $D_\omega$ consists of the integers first announced by the generator, with an input preceding the response in each round. This companion theorem establishes the exact randomized density guarantee against oblivious adversaries. The bound is on expected counts before taking the liminf; validity is not an additional conclusion of this printed theorem.
--
--   Differences from the source:
--   - encoding: positive family indices and rounds → zero-based Family and stream indices; the response at index t sees inputs 0 through t; reason: adding one identifies the indices, and causal replay also recovers the generator's own past outputs
--   - encoding: a randomized algorithm against a non-adaptive adversary → a probability space with measurable random history responses and an enumeration fixed outside the expectation; reason: presampling the private randomness represents every causal randomized strategy; countable discrete outputs require exactly measurable singleton fibres
--   - encoding: prefix-count ratios and their asymptotic lower limits → real ratios with zero at a zero denominator and Filter.liminf atTop; reason: all numerators are measurable finite counts bounded by the corresponding denominator; an infinite target has eventually positive denominators, so the total convention changes no lower density
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), Theorem 4.2, printed p.18 (PDF p.20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_randomized

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy
open DenseLanguageGeneration.PatientScope
open Filter Topology

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- Cai et al., STOC 2027 submission #335 (October 2026), Theorem 4.2,
printed p.18 (PDF p.20); proof in Appendix C, printed pp.41–46 (PDF pp.43–48).
The algorithm may depend on the family only; the oblivious adversary's target and
enumeration are quantified after it and outside the expectation (Definition 4.1). -/
theorem randomized_lower_density (L : Family) :
    ∃ R : RandomizedGenerator, ∀ (i : ℕ) (a : ℕ → ℕ+), IsEnumeration (L i) a →
      1 - Real.exp (-1) ≤ randomizedLowerDensity R (L i) a := by sorry

end DenseLanguageGeneration.PatientScope.Supplement
