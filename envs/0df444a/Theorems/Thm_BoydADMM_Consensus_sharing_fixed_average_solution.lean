-- Prove2me | Theorems.Thm_BoydADMM_Consensus_sharing_fixed_average_solution
-- name    : BoydADMM.Consensus.sharing_fixed_average_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:06:54.824583+00:00
-- url     : https://prove2.me/theorems/79dca0ed-2788-47c6-9f60-6ba0009a7067
-- title:
--   (7.13): with $\bar z$ fixed, $z_i=a_i+\bar z-\bar a$
-- statement:
--   Let $N\ge1$ and $a_1,\dots,a_N\in\mathbb R^n$, and fix $w\in\mathbb R^n$ (the value of the average $\bar z$). The problem
--   $$\operatorname*{minimize}\ \sum_{i=1}^N\|z_i-a_i\|_2^2\quad\text{subject to}\quad \frac1N\sum_{i=1}^N z_i=w$$
--   over $(z_1,\dots,z_N)$ has the unique solution
--   $$z_i=a_i+w-\bar a,\qquad i=1,\dots,N.\tag{7.13}$$
--
--   In the sharing $z$-update, with $\bar z$ fixed the term $g(N\bar z)$ is constant and the factor $\rho/2>0$ does not change the minimizers, so this is exactly the book's "minimizing over $z_1,\dots,z_N$ with $\bar z$ fixed".
--
--   **Formalization Note** The book says "has the solution"; uniqueness is also stated.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 57, §7.3, (7.13)

import Mathlib
import Definitions.Def_BoydADMM_Consensus_Model

open scoped BigOperators InnerProductSpace

namespace BoydADMM.Consensus

/-- (7.13), §7.3, p. 57: with the average `z̄ = w` fixed, the problem of minimizing
`∑_i ‖z_i − a_i‖²` over `(z_1, …, z_N)` subject to `(1/N)∑_i z_i = w` has the unique solution
`z_i = a_i + w − ā`. (With `z̄` fixed, the term `g(N z̄)` of the book's objective is constant and
the factor `ρ/2 > 0` does not change the minimizers.) -/
theorem sharing_fixed_average_solution {n N : ℕ} (hN : 0 < N)
    (a z : Fin N → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n)) :
    (avg z = w ∧ ∀ z' : Fin N → EuclideanSpace ℝ (Fin n), avg z' = w →
        ∑ i, ‖z i - a i‖ ^ 2 ≤ ∑ i, ‖z' i - a i‖ ^ 2) ↔
      ∀ i, z i = a i + w - avg a := by sorry

end BoydADMM.Consensus
