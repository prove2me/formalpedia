-- Prove2me | Theorems.Thm_AndersonAccel_Safe_norm_windowB_le
-- name    : AndersonAccel.Safe.norm_windowB_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:07:48.847474+00:00
-- url     : https://prove2.me/theorems/b8e3146b-7bb0-49dc-869e-4df37cef6e55
-- title:
--   Lemma 3.3 — $\|B_k\|_2\le 3((1+\bar\theta+\tau)/\tau)^m-2$
-- statement:
--   Let $\bar\theta,\tau\in(0,1)$ and let $m\ge1$ be the max-memory. Let $s_0,\dots,s_{m_k-1}$ and $y_0,\dots,y_{m_k-1}$ be vectors in $\mathbb R^n$ with $m_k\le m$, and let $B_k=B^{m_k}$ be the Powell-regularized matrix of (3.5). Assume
--   1. every update is well-defined: $\hat s_i^Ts_i\ne0$;
--   2. $\|y_i\|_2\le2\|s_i\|_2$;
--   3. $\|\hat s_i\|_2\ge\tau\|s_i\|_2$,
--
--   for $i=0,\dots,m_k-1$. Then, in the induced $\ell_2$ operator norm,
--   $$\|B_k\|_2\ \le\ 3\Bigl(\frac{1+\bar\theta+\tau}{\tau}\Bigr)^{m}-2.$$
--
--   The bound is uniform in the iteration and depends only on $\bar\theta$, $\tau$ and the max-memory $m$; together with Lemma 3.2 it controls the inverse matrices used by the algorithm.
--
--   **Formalization Note** The paper assumes "$m_k$ is chosen by rule (3.7)" and uses it, in the first line of its proof, only through $\|\hat s_i\|_2\ge\tau\|s_i\|_2$ and $m_k\le m$; these two consequences are the hypotheses here. The connection with rule (3.7) along the algorithm is Corollary 3.5. The exponent is the max-memory $m$, not $m_k$.
-- source:
--   Zhang, O'Donoghue, Boyd, SIAM J. Optim. 30 (2020), p. 3178, Lemma 3.3 (rule (3.7), p. 3177)

import Mathlib
import Definitions.Def_AndersonAccel_Safe_Basic
import Definitions.Def_AndersonAccel_Safe_windowB

namespace AndersonAccel.Safe

/-- Lemma 3.3 (p. 3178). Under the hypotheses of Lemma 3.2, if `‖y_i‖ ≤ 2‖s_i‖` on the window and
the window satisfies what rule (3.7) guarantees (`‖ŝ_i‖ ≥ τ‖s_i‖` and `m_k ≤ m`), then
`‖B‖ ≤ 3((1 + θ̄ + τ)/τ)^m - 2` in the operator 2-norm. -/
theorem norm_windowB_le {n : ℕ} (θbar τ : ℝ) (m : ℕ) (hθ0 : 0 < θbar) (hθ1 : θbar < 1)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hm : 1 ≤ m)
    (s y : ℕ → EuclideanSpace ℝ (Fin n)) (mk : ℕ) (hmk : mk ≤ m)
    (hwd : ∀ i < mk, inner ℝ (windowShat s i) (s i) ≠ 0)
    (hy : ∀ i < mk, ‖y i‖ ≤ 2 * ‖s i‖)
    (hτs : ∀ i < mk, τ * ‖s i‖ ≤ ‖windowShat s i‖) :
    ‖windowB θbar s y mk‖ ≤ 3 * ((1 + θbar + τ) / τ) ^ m - 2 := by sorry

end AndersonAccel.Safe
