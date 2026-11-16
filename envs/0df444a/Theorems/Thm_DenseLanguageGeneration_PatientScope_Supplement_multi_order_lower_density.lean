-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_Supplement_multi_order_lower_density
-- name    : DenseLanguageGeneration.PatientScope.Supplement.multi_order_lower_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:03:21.26082+00:00
-- url     : https://prove2.me/theorems/ca8238e1-090e-482a-a996-d59183d9175f
-- title:
--   Theorem 5.2 — Deterministic density under multiple orders
-- statement:
--   Fix a known countably indexed family $\mathcal L$ of infinite languages, a positive integer $k$, and bijections $\sigma_1,\ldots,\sigma_k$ of $\mathbb Z_{>0}$ read as sequences. There is one deterministic causal generator $G$, depending only on the family and the orders, such that for every target $K=L_i$, every legal full enumeration $a$, and every order $j$,
--
--   $$\liminf_{n\to\infty}\frac{|D\cap K\cap[n]_j|}{|K\cap[n]_j|}\ge\frac12,\qquad [n]_j=\{\sigma_j(1),\ldots,\sigma_j(n)\}.$$
--
--   Here $D$ is the set of integers first announced by the generator. The guarantee holds under all prescribed orders simultaneously against every adaptive adversary. This companion theorem extends the exact deterministic density constant to any positive finite number of orders.
--
--   Differences from the source:
--   - encoding: positive family indices and rounds → zero-based Family and stream indices; the response at index t sees inputs 0 through t; reason: adding one identifies the indices, and causal replay also recovers the generator's own past outputs
--   - encoding: the minimum of lower densities under k orders → a bound for every component indexed by Fin k, with 1 ≤ k; reason: for a positive finite collection a minimum exceeds a constant exactly when every component does; bijections are read as sequences as in the source
--   - encoding: prefix-count ratios and their asymptotic lower limits → real ratios with zero at a zero denominator and Filter.liminf atTop; reason: all numerators are measurable finite counts bounded by the corresponding denominator; an infinite target has eventually positive denominators, so the total convention changes no lower density
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), Theorem 5.2, printed p.27 (PDF p.29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_multiOrder

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy
open DenseLanguageGeneration.PatientScope
open Filter Topology

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- Cai et al., STOC 2027 submission #335 (October 2026), Theorem 5.2,
printed p.27 (PDF p.29); proof in Appendix D, printed pp.47–52 (PDF pp.49–54).
One deterministic algorithm, depending on the family and the k orders, has lower
density at least 1/2 under every order simultaneously (the minimum of Definition 5.1),
on every legal enumeration (adaptive adversary). -/
theorem multi_order_lower_density (L : Family) (k : ℕ) (hk : 1 ≤ k)
    (σ : Fin k → (ℕ+ ≃ ℕ+)) :
    ∃ G : Generator ℕ+, ∀ (i : ℕ) (a : ℕ → ℕ+), IsEnumeration (L i) a →
      ∀ j : Fin k, (1 / 2 : ℝ) ≤ orderLowerDensity G (L i) a (σ j) := by sorry

end DenseLanguageGeneration.PatientScope.Supplement
