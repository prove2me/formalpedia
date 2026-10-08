-- Prove2me | Theorems.Thm_BellmanDP_GoldMining_index_rule_multi_outcome
-- name    : BellmanDP.GoldMining.index_rule_multi_outcome
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T15:14:23.097528+00:00
-- url     : https://prove2.me/theorems/700c7995-33b7-45f4-a798-c7bfcd4d3146
-- title:
--   Chapter II, Theorem 3 — the index rule for two mines with several outcomes per use
-- statement:
--   Let $K \ge 0$ outcomes be possible for each use of the machine. For $k = 1, \dots, K$ let $p_k, q_k \ge 0$ with $\sum_k p_k < 1$ and $\sum_k q_k < 1$, and let $0 \le c_k \le 1$, $0 \le d_k \le 1$, $c'_k + c_k = 1$, $d'_k + d_k = 1$. Let $f$ be a solution, bounded in every rectangle $0 \le x \le \bar X$, $0 \le y \le \bar Y$, of
--   $$f(x,y) = \max\Bigl[A: \sum_{k=1}^{K} p_k\bigl(c_kx + f(c'_kx,\,y)\bigr),\; B: \sum_{k=1}^{K} q_k\bigl(d_ky + f(x,\,d'_ky)\bigr)\Bigr], \qquad x, y \ge 0.$$
--   Write $\alpha = \dfrac{\sum_k p_kc_k}{1-\sum_k p_k}$ and $\beta = \dfrac{\sum_k q_kd_k}{1-\sum_k q_k}$. Then at every $x, y \ge 0$: if $\alpha x > \beta y$, $f(x,y)$ equals the A-branch; if $\alpha x < \beta y$, it equals the B-branch; if $\alpha x = \beta y$, it equals both.
--
--   Theorem 2 is the case of a single outcome per use.
--
--   **Formalization Note** Outcomes are indexed by `Fin K`; the book calls their number $N$. The book's condition (2b), "$1 \ge c_k, d_k \ge 0$", is read as $0 \le c_k \le 1$ and $0 \le d_k \le 1$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter II, § 10, Theorem 3, pp. 69-70

import Mathlib
import Definitions.Def_BellmanDP_GoldMining_Model
import Definitions.Def_BellmanDP_GoldMining_MultiOutcome

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, Theorem 3, pp. 69–70: two mines, `K` outcomes per use
(the book's `N`). Under (2): `p_k, q_k ≥ 0`, `Σ p_k < 1`, `Σ q_k < 1`, `0 ≤ c_k, d_k ≤ 1`,
`c'_k + c_k = d'_k + d_k = 1`, the solution `f` of (1) (bounded in every rectangle) satisfies at
every `x, y ≥ 0`: `f = A` if `(Σ p_k c_k)/(1 − Σ p_k) x > (Σ q_k d_k)/(1 − Σ q_k) y`, `f = B` if
the reverse holds, and `f = A = B` on equality. -/
theorem index_rule_multi_outcome (K : ℕ) (p c c' q d d' : Fin K → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (hps : ∑ k, p k < 1) (hqs : ∑ k, q k < 1)
    (hc0 : ∀ k, 0 ≤ c k) (hc1 : ∀ k, c k ≤ 1) (hd0 : ∀ k, 0 ≤ d k) (hd1 : ∀ k, d k ≤ 1)
    (hc' : ∀ k, c' k + c k = 1) (hd' : ∀ k, d' k + d k = 1)
    (f : ℝ → ℝ → ℝ) (hf : IsTwoMineSolution K p c c' q d d' f) (hfb : BoundedOnRectangles f)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((∑ k, q k * d k) / (1 - ∑ k, q k) * y < (∑ k, p k * c k) / (1 - ∑ k, p k) * x →
        f x y = optA K p c c' f x y) ∧
    ((∑ k, p k * c k) / (1 - ∑ k, p k) * x < (∑ k, q k * d k) / (1 - ∑ k, q k) * y →
        f x y = optB K q d d' f x y) ∧
    ((∑ k, p k * c k) / (1 - ∑ k, p k) * x = (∑ k, q k * d k) / (1 - ∑ k, q k) * y →
        f x y = optA K p c c' f x y ∧ f x y = optB K q d d' f x y) := by sorry

end BellmanDP.GoldMining
