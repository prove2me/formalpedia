-- Prove2me | Theorems.Thm_BudgetClock_Subadditive_counting_chain
-- name    : BudgetClock.Subadditive.counting_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:23:51.618312+00:00
-- url     : https://prove2.me/theorems/3c5b907a-a97c-44bf-83ec-3fcceea57ae9
-- title:
--   Proof of Theorem 8, p. 16 — 1 ≥ 1/(|Z_1|+1) + Σ |Z_{i−1}|/(|Z_i|+1) implies |Z_r| ≥ (r/2)^r
-- statement:
--   Let $r \ge 1$ and let $z_1, \dots, z_r \ge 1$ be natural numbers with
--
--   $$\frac{1}{z_1 + 1} + \frac{z_1}{z_2 + 1} + \cdots + \frac{z_{r-1}}{z_r + 1} \le 1.$$
--
--   Then
--
--   $$z_r \ge \left(\frac{r}{2}\right)^{r}.$$
--
--   In the proof of Theorem 8, $z_i = |Z_i|$ is the size of the $i$-th block of the optimal set, and the hypothesis is what budget feasibility of the optimal set gives. The conclusion says the $r$-th block, hence the optimal set, has at least $(r/2)^r$ members, which bounds the number $r$ of blocks by roughly $\log n / \log\log n$.
--
--   **Formalization Note** The sizes are a function `z : ℕ → ℕ` read at the indices $1, \dots, r$; the sum $\sum_{i=1}^{r-1} z_i/(z_{i+1}+1)$ is written over `Finset.Ico 1 r`, which avoids natural-number subtraction and is empty for $r = 1$.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 16, proof of Theorem 8, second case (chain of inequalities ending in |Z_r| ≥ (r/2)^r)

import Mathlib

namespace BudgetClock.Subadditive

theorem counting_chain (r : ℕ) (hr : 1 ≤ r) (z : ℕ → ℕ)
    (hz : ∀ i, 1 ≤ i → i ≤ r → 1 ≤ z i)
    (hchain : 1 / ((z 1 : ℝ) + 1) +
        ∑ i ∈ Finset.Ico 1 r, (z i : ℝ) / ((z (i + 1) : ℝ) + 1) ≤ 1) :
    ((r : ℝ) / 2) ^ r ≤ (z r : ℝ) := by sorry

end BudgetClock.Subadditive
