-- Prove2me | Theorems.Thm_EdmondsKarp_Scaling_maxFlow_value_ge
-- name    : EdmondsKarp.Scaling.maxFlow_value_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:27:31.110917+00:00
-- url     : https://prove2.me/theorems/44388439-f4fd-4615-935e-cb646245ae24
-- title:
--   Proof of Theorem 9 — $f_p^* \ge \max(0, B/2^p - \max(m,n))$
-- statement:
--   Let $a_1,\dots,a_m$ and $b_1,\dots,b_n$ be natural numbers with common sum $B = \sum_i a_i = \sum_j b_j$, and let $p \ge 0$. Then
--   $$\min\Big(\sum_{i=1}^m \Big\lfloor\frac{a_i}{2^p}\Big\rfloor, \sum_{j=1}^n \Big\lfloor\frac{b_j}{2^p}\Big\rfloor\Big) \;\ge\; \max\Big(0,\ \frac{B}{2^p} - \max(m,n)\Big).$$
--
--   The left-hand side is the maximum-flow value $f_p^*$ of Problem $p$; this lower bound turns (6) into the bound of Theorem 9.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 260, proof of Theorem 9 (unnumbered display f_p* ≥ max(0, B/2^p − max(m, n)))

import Mathlib

namespace EdmondsKarp.Scaling

/-- Proof of Theorem 9 (p. 260): with `B = ∑_i a_i = ∑_j b_j`, the maximum-flow value
`f_p^* = min(∑_i [a_i/2^p], ∑_j [b_j/2^p])` of Problem `p` satisfies
`f_p^* ≥ max(0, B/2^p - max(m, n))`. -/
theorem maxFlow_value_ge {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ)
    (hsum : ∑ i, a i = ∑ j, b j) (p : ℕ) :
    max 0 (((∑ i, a i : ℕ) : ℝ) / 2 ^ p - ((max m n : ℕ) : ℝ)) ≤
      ((min (∑ i, a i / 2 ^ p) (∑ j, b j / 2 ^ p) : ℕ) : ℝ) := by sorry

end EdmondsKarp.Scaling
