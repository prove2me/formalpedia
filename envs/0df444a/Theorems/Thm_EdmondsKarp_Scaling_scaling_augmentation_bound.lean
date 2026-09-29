-- Prove2me | Theorems.Thm_EdmondsKarp_Scaling_scaling_augmentation_bound
-- name    : EdmondsKarp.Scaling.scaling_augmentation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:28:02.39923+00:00
-- url     : https://prove2.me/theorems/2f41924f-a2bc-464c-82be-4981c96457a7
-- title:
--   Theorem 9 — the scaling method uses at most $\max(m,n)(2 + [\log_2(\sum a_i/\max(m,n))])$ augmentations
-- statement:
--   Let $m, n \ge 1$, let the supplies $a_1,\dots,a_m$ and demands $b_1,\dots,b_n$ be positive integers with $\sum_i a_i = \sum_j b_j$, and let $d_{ij} \ge 0$ be the costs of the Hitchcock transportation problem. Let $l$ be such that $a_i < 2^l$ and $b_j < 2^l$ for all $i, j$. Then every run of the scaling method, which solves Problems $l-1, l-2, \dots, 0$ in turn, starting from the zero flow in Problem $l-1$ and from twice the final flow of Problem $p$ in Problem $p-1$, performs a total number of flow augmentations at most
--   $$\max(m,n)\left(2 + \left\lfloor \log_2 \frac{\sum_{i=1}^m a_i}{\max(m,n)} \right\rfloor\right).$$
--
--   The bound is roughly the number of binary digits needed to write the data, so the scaling method is a polynomial-time ("good") algorithm for the transportation problem, whereas the direct primal–dual method can take $\sum a_i$ augmentations.
--
--   **Formalization Note** The count $\sum_{p<l} K_p$ is compared in $\mathbb{Z}$ with $\max(m,n)\,(2 + \lfloor \log_2(B/\max(m,n)) \rfloor)$, using `Real.logb 2` and `Int.floor`; $B/\max(m,n) \ge 1$ under the hypotheses, so the floor is nonnegative. Positivity of the $a_i$, $b_j$ is §1.1's standing assumption that capacities are positive; without it the bound fails ($m=5$, $n=1$, $a=(1,0,0,0,0)$, $b=(1)$ needs one augmentation, while the bound is negative). A run is any sequence satisfying `IsScalingRun`; the paper's path selection rule is abstracted to its invariant (every flow pseudo-extreme), so the statement covers every run of the paper's method. The bound does not depend on $l$ or on the costs.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 260, Theorem 9

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation
import Definitions.Def_EdmondsKarp_Scaling_Run

namespace EdmondsKarp.Scaling

/-- Theorem 9 (p. 260). The number of flow augmentations in applying the scaling method to a
transportation problem with integral (positive) supplies `a_1, …, a_m` and demands `b_1, …, b_n`,
`∑ a_i = ∑ b_j`, nonnegative costs, and any `l` with all `a_i, b_j < 2^l`, is at most
`max(m, n) (2 + [log_2 (∑ a_i / max(m, n))])`, where `[·]` is the floor. -/
theorem scaling_augmentation_bound {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (a : Fin m → ℕ)
    (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hsum : ∑ i, a i = ∑ j, b j) (hd : ∀ i j, 0 ≤ d i j) (l : ℕ)
    (hla : ∀ i, a i < 2 ^ l) (hlb : ∀ j, b j < 2 ^ l) (K : ℕ → ℕ) (F : ℕ → ℕ → Flow m n)
    (hR : IsScalingRun a b d l K F) :
    ((∑ p ∈ Finset.range l, K p : ℕ) : ℤ) ≤
      ((max m n : ℕ) : ℤ) *
        (2 + ⌊Real.logb 2 (((∑ i, a i : ℕ) : ℝ) / ((max m n : ℕ) : ℝ))⌋) := by sorry

end EdmondsKarp.Scaling
