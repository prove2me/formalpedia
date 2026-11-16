-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_Supplement_multi_order_block_lower_density
-- name    : DenseLanguageGeneration.PatientScope.Supplement.multi_order_block_lower_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:04:17.236663+00:00
-- url     : https://prove2.me/theorems/96dacc0c-1ea4-4d43-894d-bade91318856
-- title:
--   Theorem 5.3 — Fixed-block multi-order bound and its limit
-- statement:
--   Fix a positive number $k$ of orders and define
--
--   $$h_k(m)=1-\frac{4(km+1)^{1-1/k}+1}{m}.$$
--
--   For every positive integer $m$, every countably indexed family $\mathcal L$ of infinite languages and every collection of $k$ bijections $\sigma_j$ of $\mathbb Z_{>0}$, there is a deterministic causal generator $G$ such that, for every target $K=L_i$, full enumeration $a$ and order $j$,
--
--   $$\liminf_{n\to\infty}\frac{|D\cap K\cap[n]_j|}{|K\cap[n]_j|}\ge\frac{h_k(m)}2.$$
--
--   For each fixed positive $k$, the theorem also asserts
--
--   $$\lim_{m\to\infty}\frac{h_k(m)}2=\frac12.$$
--
--   The chosen generator may depend on the family, the orders and $m$, before the target and enumeration are chosen. The exponent is real. The bound applies even when $h_k(m)\le0$. This companion theorem records the entire finite-parameter guarantee and its asymptotic conclusion.
--
--   Differences from the source:
--   - encoding: positive family indices and rounds → zero-based Family and stream indices; the response at index t sees inputs 0 through t; reason: adding one identifies the indices, and causal replay also recovers the generator's own past outputs
--   - encoding: the minimum of lower densities under k orders → a bound for every component indexed by Fin k, with 1 ≤ k; reason: for a positive finite collection a minimum exceeds a constant exactly when every component does; bijections are read as sequences as in the source
--   - encoding: prefix-count ratios and their asymptotic lower limits → real ratios with zero at a zero denominator and Filter.liminf atTop; reason: all numerators are measurable finite counts bounded by the corresponding denominator; an infinite target has eventually positive denominators, so the total convention changes no lower density
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), Theorem 5.3, printed pp.27–28 (PDF pp.29–30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_multiOrder

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy
open DenseLanguageGeneration.PatientScope
open Filter Topology

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- Cai et al., STOC 2027 submission #335 (October 2026), Theorem 5.3,
printed pp.27–28 (PDF pp.29–30); proof printed pp.28–34 (PDF pp.30–36).
For each fixed number k ≥ 1 of orders: the bound h(m)/2 = pairedBound k m / 2 (no
positivity assumed), and the limit conjunct h(m)/2 → 1/2. -/
theorem multi_order_block_lower_density (k : ℕ) (hk : 1 ≤ k) :
    (∀ m : ℕ, 1 ≤ m → ∀ (L : Family) (σ : Fin k → (ℕ+ ≃ ℕ+)), ∃ G : Generator ℕ+,
      ∀ (i : ℕ) (a : ℕ → ℕ+), IsEnumeration (L i) a →
        ∀ j : Fin k, pairedBound k m / 2 ≤ orderLowerDensity G (L i) a (σ j)) ∧
    Tendsto (fun m : ℕ => pairedBound k m / 2) atTop (𝓝 (1 / 2)) := by sorry

end DenseLanguageGeneration.PatientScope.Supplement
