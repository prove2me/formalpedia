-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_Supplement_randomized_multi_order_lower_density
-- name    : DenseLanguageGeneration.PatientScope.Supplement.randomized_multi_order_lower_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:04:41.729567+00:00
-- url     : https://prove2.me/theorems/31de6b08-5890-4a8b-abea-a2176aff8808
-- title:
--   Theorem 5.9 — Randomized density under multiple orders
-- statement:
--   For every known countably indexed family $\mathcal L$ of infinite languages, every positive integer $k$ and every collection of bijections $\sigma_1,\ldots,\sigma_k$ of $\mathbb Z_{>0}$, there is one randomized causal generator $R$ such that for every target $K=L_i$, every full enumeration $a$ fixed independently of the private randomness, and every order $j$,
--
--   $$\liminf_{n\to\infty}\frac{\mathbb E_\omega[|D_\omega\cap K\cap[n]_j|]}{|K\cap[n]_j|}\ge1-e^{-1}.$$
--
--   The generator is chosen from the family and orders alone and provides the guarantee under all orders simultaneously. This companion theorem combines the exact randomized constant with the multiple-order setting, using Definition 5.8's expectation before liminf.
--
--   Differences from the source:
--   - encoding: positive family indices and rounds → zero-based Family and stream indices; the response at index t sees inputs 0 through t; reason: adding one identifies the indices, and causal replay also recovers the generator's own past outputs
--   - encoding: a randomized algorithm against a non-adaptive adversary → a probability space with measurable random history responses and an enumeration fixed outside the expectation; reason: presampling the private randomness represents every causal randomized strategy; countable discrete outputs require exactly measurable singleton fibres
--   - encoding: the minimum of lower densities under k orders → a bound for every component indexed by Fin k, with 1 ≤ k; reason: for a positive finite collection a minimum exceeds a constant exactly when every component does; bijections are read as sequences as in the source
--   - encoding: prefix-count ratios and their asymptotic lower limits → real ratios with zero at a zero denominator and Filter.liminf atTop; reason: all numerators are measurable finite counts bounded by the corresponding denominator; an infinite target has eventually positive denominators, so the total convention changes no lower density
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), Theorem 5.9, printed p.35 (PDF p.37); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_multiOrder

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy
open DenseLanguageGeneration.PatientScope
open Filter Topology

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- Cai et al., STOC 2027 submission #335 (October 2026), Theorem 5.9,
printed p.35 (PDF p.37); proof in Appendix E, printed pp.52–58 (PDF pp.54–60).
Lower density under k orders of a randomized algorithm (Definition 5.8), against
every non-adaptive adversary, at least 1 − 1/e under every order. -/
theorem randomized_multi_order_lower_density (L : Family) (k : ℕ) (hk : 1 ≤ k)
    (σ : Fin k → (ℕ+ ≃ ℕ+)) :
    ∃ R : RandomizedGenerator, ∀ (i : ℕ) (a : ℕ → ℕ+), IsEnumeration (L i) a →
      ∀ j : Fin k, 1 - Real.exp (-1) ≤ randomizedOrderLowerDensity R (L i) a (σ j) := by sorry

end DenseLanguageGeneration.PatientScope.Supplement
