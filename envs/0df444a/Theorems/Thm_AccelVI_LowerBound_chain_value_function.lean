-- Prove2me | Theorems.Thm_AccelVI_LowerBound_chain_value_function
-- name    : AccelVI.LowerBound.chain_value_function
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:59.794393+00:00
-- url     : https://prove2.me/theorems/8a3bfcc3-9f90-4b0e-aa44-02d8a43e80db
-- title:
--   Proof of Theorem 6.3, p. 12 — on the chain of Figure 1 the value function is v*_i = λ^{i−1}/(1 − λ)
-- statement:
--   Let $n \in \mathbb{N}$, $\lambda \in (0,1)$, and let $T$ be the Bellman operator of the $n$-state chain of Figure 1 (state 1 absorbing with reward 1, state $i \ge 2$ moving to $i - 1$ with reward 0, one action). The vector
--   $$
--   v^*_i = \frac{\lambda^{i-1}}{1 - \lambda}, \qquad i = 1, \dots, n,
--   $$
--   is a fixed point of $T$, and it is the only one: every $u \in \mathbb{R}^n$ with $T(u) = u$ equals $v^*$.
--
--   Since the paper defines the optimal value function as the unique fixed point of $T$, this identifies it explicitly on the hard instance; the lower bound of Theorem 6.3 reads off its entries $v^*_i$ with $i \ge s + 1$.
--
--   **Formalization Note.** States are 0-based (`Fin n`): the paper's $v^*_i = \lambda^{i-1}/(1-\lambda)$ is `lam ^ k / (1 - lam)` at `k = i − 1`. The uniqueness clause states the page's "the value function is" for the fixed-point definition of $v^*$ on p. 3.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 12, proof of Theorem 6.3, first sentence after Figure 1

import Mathlib
import Definitions.Def_AccelVI_LowerBound_Setting

namespace AccelVI.LowerBound
theorem chain_value_function (n : ℕ) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    bellman (chainMDP n lam) (fun k : Fin n => lam ^ (k : ℕ) / (1 - lam)) =
      (fun k : Fin n => lam ^ (k : ℕ) / (1 - lam)) ∧
    ∀ u : Fin n → ℝ, bellman (chainMDP n lam) u = u →
      u = (fun k : Fin n => lam ^ (k : ℕ) / (1 - lam)) := by sorry
end AccelVI.LowerBound
