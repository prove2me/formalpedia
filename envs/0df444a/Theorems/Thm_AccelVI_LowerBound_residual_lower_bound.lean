-- Prove2me | Theorems.Thm_AccelVI_LowerBound_residual_lower_bound
-- name    : AccelVI.LowerBound.residual_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:57.905979+00:00
-- url     : https://prove2.me/theorems/84bdab54-2446-433d-ab34-3645a0123557
-- title:
--   (6.2)–(6.4), p. 12 — on the chain, first-order iterates have ‖v_s − T(v_s)‖∞ ≥ λ^s for 1 ≤ s ≤ n − 1
-- statement:
--   Let $n \in \mathbb{N}$, $\lambda \in (0,1)$, let $T$ be the Bellman operator of the $n$-state chain of Figure 1, and let $(v_s)_{s \ge 0}$ be first-order iterates for $T$. Then for every $s$ with $1 \le s \le n - 1$,
--   $$
--   \|v_s - T(v_s)\|_\infty \ge \lambda^s .
--   $$
--
--   This is the chain of inequalities (6.2)–(6.4) in the proof of Theorem 6.3: the residual of any first-order iterate stays above $\lambda^s$ for the first $n - 1$ steps.
--
--   **Formalization Note.** $\|\cdot\|_\infty$ is Mathlib's sup norm on `Fin n → ℝ`; $n - 1$ is natural-number subtraction, so with $1 \le s$ the hypotheses force $n \ge 2$ and $s < n$.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 12, proof of Theorem 6.3, displays (6.2)–(6.4)

import Mathlib
import Definitions.Def_AccelVI_LowerBound_Setting

namespace AccelVI.LowerBound
theorem residual_lower_bound (n : ℕ) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) (v : ℕ → Fin n → ℝ)
    (hv : IsFirstOrder (bellman (chainMDP n lam)) v) (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s ≤ n - 1) :
    lam ^ s ≤ ‖v s - bellman (chainMDP n lam) (v s)‖ := by sorry
end AccelVI.LowerBound
