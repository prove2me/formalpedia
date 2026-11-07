-- Prove2me | Theorems.Thm_EffHorizonProphet_lemma_14
-- name    : EffHorizonProphet.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:49.63678+00:00
-- url     : https://prove2.me/theorems/89b69238-a7db-4064-990d-3a4da8b18400
-- title:
--   Lemma 14 — second moment of the truncated geometric law
-- statement:
--   Let $S\ge1$ and $r\in[0,1)$, and let $K$ have the truncated geometric law on $\{0,\dots,S-1\}$. With $\Delta(K)=(\mathbb E[K])^2-\mathrm{Var}(K)=2(\mathbb E[K])^2-\mathbb E[K^2]$,
--   $$\Delta(K)\ge-\mathbb E[K],\qquad\text{equivalently}\qquad\mathbb E[K^2]\le2(\mathbb E[K])^2+\mathbb E[K].$$
--
--   This is the second bound used in the variance estimate behind Lemma 12.
--
--   Differences from the source:
--   - encoding: $\mathbb E[K^k]$ for a random variable $K$, and $\Delta(K)$ → ratios of finite sums, with $\Delta(K)$ written as $2(\mathbb E[K])^2-\mathbb E[K^2]$; reason: these are the expectations under the printed law, and the second expression is the one on the page (p.25)
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Lemma 14, p.25

import Mathlib
import Definitions.Def_EffHorizonProphet_truncGeomMoment

namespace EffHorizonProphet

/-- **Lemma 14** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.25): for `K` truncated geometric on `{0, …, S-1}` with `r ∈ [0, 1)`,
`Δ(K) ≥ -E[K]`, equivalently `E[K²] ≤ 2(E[K])² + E[K]`, where `Δ(Z) = (E[Z])² - Var(Z)`.

**Formalization Note** `Δ(K)` is written out as `2(E[K])² - E[K²]`, the page's second expression. -/
theorem lemma_14 (S : ℕ) (hS : 1 ≤ S) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    -truncGeomMoment S r 1 ≤ 2 * truncGeomMoment S r 1 ^ 2 - truncGeomMoment S r 2 ∧
      truncGeomMoment S r 2 ≤ 2 * truncGeomMoment S r 1 ^ 2 + truncGeomMoment S r 1 := by sorry

end EffHorizonProphet
