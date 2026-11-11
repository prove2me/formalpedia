-- Prove2me | Theorems.Thm_ConcurrentStochasticApprox_Approx_lemma_5_4
-- name    : ConcurrentStochasticApprox.Approx.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:54.772203+00:00
-- url     : https://prove2.me/theorems/9c204c2d-8aff-4fc2-a3be-d70449e531a4
-- title:
--   Lemma 5.4 — support-preserving approximation of distributions in $D(t\ell,B)$
-- statement:
--   Let $t\ge1$ and $2^B\ge\ell\ge2$, and let $\mu\in\Delta([t])$ be a distribution with
--   $$\mathrm{Patience}(\mu)<2^{2^B-\ell}.$$
--   Then there is a distribution $\mu'\in D(t\ell,B)$ with $\mathrm{supp}(\mu')=\mathrm{supp}(\mu)$ and $\mathrm{rel}(\mu,\mu')\le t\cdot2^{1-\ell}$.
--
--   This converts strategies of bounded patience into power-series representable strategies with the same support and a small relative error.
--
--   Differences from the source:
--   - encoding: [t] = {1, …, t} → Fin t; reason: relabelling
--   - encoding: rel(x, x') ∈ [0, ∞] with rel(x, 0) = rel(0, x) = ∞ for x > 0 → rel valued in ℝ≥0∞ (ENNReal); reason: the infinite case is represented exactly; no instance changes
-- source:
--   Ali Asadi, Krishnendu Chatterjee, The Computational Complexity of Concurrent Stochastic Games: Exact Value and Approximation, STOC 2027 submission #285 (October 2026), SHA-256 5cff187cf6b230b3bdfe540f2832f824d1ddb6acb43239fbf469d37c43b0d461, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/285.pdf, Lemma 5.4, printed p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_ConcurrentStochasticApprox_Approx_PowerSeries
open Finset

namespace ConcurrentStochasticApprox.Approx

/-- **Lemma 5.4 (Distribution approximation).** Let `t ≥ 1`, `2^B ≥ ℓ ≥ 2`, and let `μ ∈ Δ([t])` with
`Patience(μ) < 2^{2^B - ℓ}`. Then there is `μ' ∈ D(tℓ, B)` with `supp(μ') = supp(μ)` and
`rel(μ, μ') ≤ t · 2^{1-ℓ}`. -/
theorem lemma_5_4 (t ℓ B : ℕ) (ht : 1 ≤ t) (hℓ2 : 2 ≤ ℓ) (hℓB : ℓ ≤ 2 ^ B) (μ : Fin t → ℝ)
    (hμ : IsDist μ) (hpat : patience μ < (2 : ℝ) ^ (2 ^ B - ℓ)) :
    ∃ μ' : Fin t → ℝ, μ' ∈ Dset t (t * ℓ) B ∧ supp μ' = supp μ ∧
      relDist μ μ' ≤ ENNReal.ofReal ((t : ℝ) * (2 : ℝ) ^ (1 - (ℓ : ℤ))) := by sorry

end ConcurrentStochasticApprox.Approx
