-- Prove2me | Theorems.Thm_CachingML_PredMarker_expected_chainLen_le
-- name    : CachingML.PredMarker.expected_chainLen_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T16:14:27.472324+00:00
-- url     : https://prove2.me/theorems/ce19f8d3-40f6-44f9-bdb9-20371c8bf4e0
-- title:
--   Lemma 3.4 — the expected length of a chain is at most $\min(1 + 2S_\ell(\eta_{r,c}), 2H_k)$
-- statement:
--   Let $k \ge 1$, let $\ell \ge 0$ be a loss function, and let $S$ be concave on $[0,\infty)$, continuous at $0$ from the right, with $S_\ell(m) \le S(m) < \infty$ for every $m \ge 0$. Run Predictive Marker with cache size $k$ and any admissible tie-breaking rule on a request sequence $\sigma$ with predictions $h$. Then for every phase $r$ and every chain index $c$,
--
--   $$\mathbb E\bigl[n(r,c)\bigr] \le \mathbb E\Bigl[\min\bigl(1 + 2 S(\eta_{r,c}),\ 2H_k\bigr)\Bigr],$$
--
--   where $n(r,c)$ is the length of chain $c$ of phase $r$, $\eta_{r,c}$ the cumulative error of the predictor on the elements evicted into it, $H_k = 1 + \tfrac12 + \dots + \tfrac1k$, and both expectations are over the random evictions of the algorithm.
--
--   The bound combines the two regimes of a chain: while it follows the predictions its length is controlled by the spread (Lemma 3.3), and once it switches to uniform evictions the special-marking argument (Lemma 3.2) caps its expected length at $2H_k$. Summed over all chains it gives the upper bound on the cost of Predictive Marker in Theorem 3.3.
--
--   **Formalization Note** The paper prints the cap as $2\log k$; its proof establishes $2H_k$ ("capping in expectation the total length by $2H_k \le 2\log k$"), and $2H_k \le 2\log k$ is false (for the natural logarithm at every $k \ge 1$; in any base at $k = 1$). Theorem 3.3 uses $2H_k$, which is what is stated. Since which elements join a chain depends on the coin flips, $\eta_{r,c}$ is random, and the minimum sits inside the expectation. Chains that do not exist have length $0$ and error $0$. As in Lemma 3.3, the spread is replaced by a concave majorant $S$ continuous at $0$. Expectations are sums over the final-state distribution, in $[0, \infty]$.
-- source:
--   Lykouris, Vassilvitskii, Competitive Caching with Machine Learned Advice, arXiv:1802.05399v4, p. 15, Lemma 3.4 and its proof

import Mathlib
import Definitions.Def_CachingML_PredMarker_spread
import Definitions.Def_CachingML_PredMarker_predictiveMarker

open scoped ENNReal

namespace CachingML.PredMarker

/-- Lemma 3.4 of Lykouris–Vassilvitskii (arXiv:1802.05399v4, p. 15), with the printed `2 log k`
replaced by the `2 H_k` its proof establishes: for every phase `r` and chain index `c`, the expected
length of the chain is at most the expectation of `min(1 + 2 S(η_{r,c}), 2 H_k)`, both expectations
over the random evictions of Predictive Marker. -/
theorem expected_chainLen_le {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (ℓ : ℝ → ℝ → ℝ) (hℓ : ∀ a b, 0 ≤ ℓ a b)
    (S : ℝ → ℝ) (hSconc : ConcaveOn ℝ (Set.Ici 0) S)
    (hScont : ContinuousWithinAt S (Set.Ici 0) 0)
    (hspread : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    (tb : PMState α → α) (htb : IsMaxTieBreak tb)
    (σ : List α) (h : Fin σ.length → ℝ) (r c : ℕ) :
    ∑' s, run k tb σ h s * (s.chainLen r c : ℝ≥0∞) ≤
      ∑' s, run k tb σ h s *
        ENNReal.ofReal (min (1 + 2 * S (chainError ℓ σ h s r c)) (2 * (harmonic k : ℝ))) := by sorry

end CachingML.PredMarker
