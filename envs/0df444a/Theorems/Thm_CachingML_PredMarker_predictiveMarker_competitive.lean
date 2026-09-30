-- Prove2me | Theorems.Thm_CachingML_PredMarker_predictiveMarker_competitive
-- name    : CachingML.PredMarker.predictiveMarker_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T16:18:20.515687+00:00
-- url     : https://prove2.me/theorems/3f23b092-40e7-48ce-a6f4-84d0116a4f2d
-- title:
--   Theorem 3.3 — Predictive Marker is $2\min(1 + 2S_\ell(\epsilon), 2H_k)$-competitive
-- statement:
--   Consider caching with cache size $k \ge 1$ and next-arrival predictions. Let $\ell \ge 0$ be a loss function whose spread is bounded by a concave function: $S$ is concave on $[0, \infty)$, continuous at $0$ from the right, and for every $m \ge 0$ the spread $S_\ell(m)$ is finite with $S_\ell(m) \le S(m)$. Let $\epsilon \ge 0$. Then for every admissible tie-breaking rule of Predictive Marker, every request sequence $\sigma$ and every prediction sequence $h$ whose error satisfies $\eta_\ell(h, \sigma) \le \epsilon \cdot \mathrm{Opt}(\sigma)$,
--
--   $$\mathbb E\bigl[\mathrm{cost}_{PM}(\sigma)\bigr] \le 2 \cdot \min\bigl(1 + 2S(\epsilon),\ 2H_k\bigr) \cdot \mathrm{Opt}(\sigma),$$
--
--   where $\mathrm{cost}_{PM}(\sigma)$ is the number of misses of Predictive Marker, the expectation is over its random evictions, $\mathrm{Opt}(\sigma)$ is the offline optimum from the empty cache, and $H_k = 1 + \tfrac12 + \dots + \tfrac1k$. In the paper's notation, $\mathrm{cr}_{PM,\ell}(\epsilon) \le 2 \cdot \min(1 + 2S_\ell(\epsilon), 2H_k)$.
--
--   The bound interpolates between consistency and robustness: with an accurate predictor the ratio is a constant depending only on the error, and with an arbitrarily bad one it is still $4H_k$, within a constant factor of the best possible for randomized caching.
--
--   **Formalization Note** The paper's competitive ratio is a maximum over sequences $\sigma$ and $\epsilon$-accurate predictors $h$; the hypothesis here is the pointwise condition $\eta_\ell(h,\sigma) \le \epsilon\,\mathrm{Opt}(\sigma)$ on the given pair, which every $\epsilon$-accurate predictor satisfies on every $\sigma$, and which is what the proof uses. The ratio is written as a product, so $\mathrm{Opt}(\sigma) = 0$ (the empty sequence) needs no special case. Predictions are arbitrary reals, one per request (the features of the paper's predictor $h : X \to Y$ are arbitrary). The tie-breaking of the arg max in Algorithm 1 is left open by the paper; the theorem holds for every admissible rule. Algorithm 1 is implemented with its eviction performed after the clean branch as well (a printed slip; see the definition). The spread majorant $S$ is applied at real arguments and is assumed continuous at $0$, which the paper does not state; without it Lemma 3.3 fails for losses whose minimal reversed-order loss stays $0$ for several lengths (see Lemma 3.3), and the paper's argument does not cover the case $\epsilon = 0$ for such losses. A concave function on $[0,\infty)$ that is at least $1$ is nondecreasing, so no monotonicity is assumed. The expected cost is a sum over the final-state distribution in $[0,\infty]$, compared with the real bound through `ENNReal.ofReal`.
-- source:
--   Lykouris, Vassilvitskii, Competitive Caching with Machine Learned Advice, arXiv:1802.05399v4, p. 14, Theorem 3.3 (proof p. 16); competitive ratio p. 5, §2.1; Definitions 2–3, pp. 7–8

import Mathlib
import Definitions.Def_CachingML_PredMarker_predError
import Definitions.Def_CachingML_PredMarker_opt
import Definitions.Def_CachingML_PredMarker_spread
import Definitions.Def_CachingML_PredMarker_predictiveMarker

open scoped ENNReal

namespace CachingML.PredMarker

/-- Theorem 3.3 of Lykouris–Vassilvitskii (arXiv:1802.05399v4, p. 14): for cache size `k ≥ 1`, a
nonnegative loss `ℓ` whose spread is bounded by a concave function `S` (continuous at `0`), and any
`ε ≥ 0`, Predictive Marker (with any tie-breaking of its `arg max`) satisfies, on every request sequence
`σ` and prediction sequence `h` with error `η_ℓ(h, σ) ≤ ε · Opt(σ)`,
`E[cost_PM(σ)] ≤ 2 · min(1 + 2 S(ε), 2 H_k) · Opt(σ)`. -/
theorem predictiveMarker_competitive {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (ℓ : ℝ → ℝ → ℝ) (hℓ : ∀ a b, 0 ≤ ℓ a b)
    (S : ℝ → ℝ) (hSconc : ConcaveOn ℝ (Set.Ici 0) S)
    (hScont : ContinuousWithinAt S (Set.Ici 0) 0)
    (hspread : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    (ε : ℝ) (hε : 0 ≤ ε)
    (tb : PMState α → α) (htb : IsMaxTieBreak tb)
    (σ : List α) (h : Fin σ.length → ℝ)
    (hacc : predError ℓ σ h ≤ ε * (opt k σ : ℝ)) :
    expCost k tb σ h ≤
      ENNReal.ofReal (2 * min (1 + 2 * S ε) (2 * (harmonic k : ℝ)) * (opt k σ : ℝ)) := by sorry

end CachingML.PredMarker
