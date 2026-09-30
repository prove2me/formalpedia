-- Prove2me | Theorems.Thm_CachingML_PredMarker_chainLen_le_one_add_spread
-- name    : CachingML.PredMarker.chainLen_le_one_add_spread
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T16:10:58.454744+00:00
-- url     : https://prove2.me/theorems/fc7a363a-831d-4648-be31-2817834f4628
-- title:
--   Lemma 3.3 — a chain of prediction-based evictions has length at most $1 + S_\ell(\eta_{r,c})$
-- statement:
--   Let $k \ge 1$, let $\ell \ge 0$ be a loss function, and let $S : \mathbb R \to \mathbb R$ be concave on $[0,\infty)$, continuous at $0$ from the right, and an upper bound for the spread: for every $m \ge 0$ the spread $S_\ell(m)$ is finite and $S_\ell(m) \le S(m)$. Run Predictive Marker with cache size $k$ and any admissible tie-breaking rule on a request sequence $\sigma$ with predictions $h$. Then on every possible outcome of the run, for every phase $r$ and every chain $c$ of that phase whose evictions were all prediction-based (no random eviction of line 21),
--
--   $$n(r,c) \le 1 + S(\eta_{r,c}),$$
--
--   where $n(r,c)$ is the length of the chain and $\eta_{r,c}$ the cumulative error of the predictor on the elements evicted into it.
--
--   This is the robustness core of the analysis: as long as a chain follows the predictions, its length is controlled by the error the predictor made on that chain alone.
--
--   **Formalization Note** The paper states the bound for "the expected length of any chain" with $S_\ell$ the spread itself. Its proof treats chains that evict by the predictions only, and shows the bound on every outcome; this is what is stated, while chains that switch to random evictions are covered by Lemma 3.4. The spread is replaced by a concave majorant $S$, as in Theorem 3.3. Continuity of $S$ at $0$ is an added hypothesis: for a loss whose minimal reversed-order loss stays $0$ over several lengths (for instance $\ell(a,b) = 0$ when $|a - b| \le 2$ and $|a-b|$ otherwise), $S_\ell(0) = 1$ while a chain can have several zero-error prediction-based evictions, so the bound fails for a majorant with $S(0) = 1$ that jumps up right after $0$. Continuity at $0$ excludes this; on $(0,\infty)$ a concave function is continuous anyway. Chains that do not exist have length $0$.
-- source:
--   Lykouris, Vassilvitskii, Competitive Caching with Machine Learned Advice, arXiv:1802.05399v4, p. 15, Lemma 3.3 and its proof

import Mathlib
import Definitions.Def_CachingML_PredMarker_spread
import Definitions.Def_CachingML_PredMarker_predictiveMarker

namespace CachingML.PredMarker

/-- Lemma 3.3 of Lykouris–Vassilvitskii (arXiv:1802.05399v4, p. 15), in the pointwise form its proof
establishes: on every outcome of a run of Predictive Marker, every chain `(r, c)` that made no random
eviction has length `n(r, c) ≤ 1 + S(η_{r,c})`, for any concave `S` on `[0, ∞)`, continuous at `0`, that
bounds the spread of the loss `ℓ` from above. -/
theorem chainLen_le_one_add_spread {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (ℓ : ℝ → ℝ → ℝ) (hℓ : ∀ a b, 0 ≤ ℓ a b)
    (S : ℝ → ℝ) (hSconc : ConcaveOn ℝ (Set.Ici 0) S)
    (hScont : ContinuousWithinAt S (Set.Ici 0) 0)
    (hspread : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    (tb : PMState α → α) (htb : IsMaxTieBreak tb)
    (σ : List α) (h : Fin σ.length → ℝ)
    (s : PMState α) (hs : s ∈ (run k tb σ h).support) (r c : ℕ) (hc : (r, c) ∉ s.randomChains) :
    (s.chainLen r c : ℝ) ≤ 1 + S (chainError ℓ σ h s r c) := by sorry

end CachingML.PredMarker
