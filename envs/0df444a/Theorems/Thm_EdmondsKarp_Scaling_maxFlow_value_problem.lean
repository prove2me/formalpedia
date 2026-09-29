-- Prove2me | Theorems.Thm_EdmondsKarp_Scaling_maxFlow_value_problem
-- name    : EdmondsKarp.Scaling.maxFlow_value_problem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:26:57.118773+00:00
-- url     : https://prove2.me/theorems/fb992fdf-ebdd-4e17-9328-924384b5d194
-- title:
--   Proof of Theorem 9 — the maximum-flow value of Problem $p$ is $\min(\sum_i [a_i/2^p], \sum_j [b_j/2^p])$
-- statement:
--   Let $a_1,\dots,a_m$ and $b_1,\dots,b_n$ be positive integers with $\sum_i a_i = \sum_j b_j$ ($m, n \ge 1$), let $d_{ij} \ge 0$, and let $p \ge 0$. Problem $p$ has a maximum flow, and every maximum flow $f$ of Problem $p$ has value
--   $$f_p^* = f(t,s) = \min\Big(\sum_{i=1}^m \Big\lfloor \frac{a_i}{2^p}\Big\rfloor,\ \sum_{j=1}^n \Big\lfloor \frac{b_j}{2^p}\Big\rfloor\Big) \ge 0.$$
--
--   The number of augmentations in a phase of the scaling method is bounded by the gap between this value and the value of the phase's initial flow.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 260, proof of Theorem 9 (unnumbered display defining f_p*)

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation
import Definitions.Def_EdmondsKarp_Scaling_Run

namespace EdmondsKarp.Scaling

/-- Proof of Theorem 9 (p. 260): Problem `p` has a maximum flow, and the value `f_p^*` of every
maximum flow of Problem `p` is `min(∑_i [a_i/2^p], ∑_j [b_j/2^p])`. -/
theorem maxFlow_value_problem {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (a : Fin m → ℕ)
    (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hsum : ∑ i, a i = ∑ j, b j) (hd : ∀ i j, 0 ≤ d i j) (p : ℕ) :
    (∃ x : Flow m n, IsMaxFlow (problem a b d p) x) ∧
      ∀ x : Flow m n, IsMaxFlow (problem a b d p) x →
        x.ret = ((min (∑ i, a i / 2 ^ p) (∑ j, b j / 2 ^ p) : ℕ) : ℝ) := by sorry

end EdmondsKarp.Scaling
