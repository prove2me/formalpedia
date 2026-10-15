-- Prove2me | Theorems.Thm_AccelVI_LowerBound_support_recursion
-- name    : AccelVI.LowerBound.support_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:08.85388+00:00
-- url     : https://prove2.me/theorems/3d8680f8-7feb-494b-b0d9-2ff7d6ba7811
-- title:
--   Proof of Theorem 6.3, p. 12 — first-order iterates on the chain satisfy v_{s,i} = 0 for i ≥ s + 1
-- statement:
--   Let $n \in \mathbb{N}$, $\lambda \in (0,1)$, let $T$ be the Bellman operator of the $n$-state chain of Figure 1, and let $(v_s)_{s \ge 0}$ be first-order iterates for $T$: $v_0 = 0$ and $v_{s+1} \in \operatorname{span}\{v_0, \dots, v_s, T(v_0), \dots, T(v_s)\}$. Then for every $s \ge 0$ and every state $i$,
--   $$
--   v_{s,i} = 0 \quad \text{whenever } i \ge s + 1 .
--   $$
--
--   The reward sits only at state 1 and moves one state per application of $T$; this support property is what forces every first-order method to need $s$ steps before it sees state $s+1$.
--
--   **Formalization Note.** States are 0-based: the paper's state $i$ is index $k = i - 1$, so "$i \ge s + 1$" is $s \le k$.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 12, proof of Theorem 6.3, recursion paragraph

import Mathlib
import Definitions.Def_AccelVI_LowerBound_Setting

namespace AccelVI.LowerBound
theorem support_recursion (n : ℕ) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) (v : ℕ → Fin n → ℝ)
    (hv : IsFirstOrder (bellman (chainMDP n lam)) v) (s : ℕ) (k : Fin n) (hk : s ≤ (k : ℕ)) :
    v s k = 0 := by sorry
end AccelVI.LowerBound
