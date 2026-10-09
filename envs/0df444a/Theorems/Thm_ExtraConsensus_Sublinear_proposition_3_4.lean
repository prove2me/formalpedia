-- Prove2me | Theorems.Thm_ExtraConsensus_Sublinear_proposition_3_4
-- name    : ExtraConsensus.Sublinear.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:46.213092+00:00
-- url     : https://prove2.me/theorems/be4b5433-e7af-49ca-a7f0-f95121fd438b
-- title:
--   Proposition 3.4, p. 12 — a nonnegative summable sequence tends to 0, has averages O(1/k) and running minima o(1/k)
-- statement:
--   Let $(a_k)_{k\ge0}$ be a real sequence with $a_k\ge0$ for all $k$ and $\sum_{t}a_t<\infty$. Then
--
--   1. $\lim_{k\to\infty}a_k=0$;
--   2. $\displaystyle\frac1k\sum_{t=1}^k a_t=O\!\left(\frac1k\right)$;
--   3. $\displaystyle\min_{1\le t\le k}a_t=o\!\left(\frac1k\right)$ as $k\to\infty$.
--
--   This elementary fact converts the summability of the progress and residual sequences into the ergodic $O(1/k)$ and running-best $o(1/k)$ rates of Theorem 3.5.
--
--   **Formalization Note** Summability is over all $t\ge0$, which is equivalent to the page's $\sum_{t=1}^\infty a_t<\infty$. The running minimum ranges over $1\le t\le k$, the same indices as the sums; its value at $k=0$ is irrelevant.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, Proposition 3.4, p. 12

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Sublinear

open Matrix Filter Topology Asymptotics

/-- Proposition 3.4, p. 12. If `aₖ ≥ 0` for all `k` and `Σₜ aₜ < ∞`, then (i) `aₖ → 0`;
(ii) `(1/k) Σ_{t=1}^{k} aₜ = O(1/k)`; (iii) `min_{1≤t≤k} aₜ = o(1/k)`. -/
theorem proposition_3_4 (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hsum : Summable a) :
    Tendsto a atTop (𝓝 0) ∧
      (fun k : ℕ => (1 / (k : ℝ)) * ∑ t ∈ Finset.Icc 1 k, a t) =O[atTop]
        (fun k : ℕ => (1 : ℝ) / k) ∧
      (fun k : ℕ => runMin a k) =o[atTop] (fun k : ℕ => (1 : ℝ) / k) := by sorry

end ExtraConsensus.Sublinear
