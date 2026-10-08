-- Prove2me | Theorems.Thm_BoydADMM_Consensus_consensus_z_update_average
-- name    : BoydADMM.Consensus.consensus_z_update_average
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:06:13.996304+00:00
-- url     : https://prove2.me/theorems/fab85582-0db9-468b-ab8c-d392db94d22f
-- title:
--   Consensus ADMM: the $z$-update is $z^{k+1}=\bar x^{k+1}+(1/\rho)\bar y^k$
-- statement:
--   Consider global variable consensus with $N\ge1$ agents and $\rho>0$. Fix $x_1,\dots,x_N\in\mathbb R^n$ (the new local iterates $x_i^{k+1}$) and $y_1,\dots,y_N\in\mathbb R^n$ (the dual variables $y_i^k$). The $z$-update of ADMM minimizes the augmented Lagrangian
--   $$L_\rho(x_1,\dots,x_N,z,y)=\sum_{i=1}^N\big(f_i(x_i)+y_i^T(x_i-z)+(\rho/2)\|x_i-z\|_2^2\big)$$
--   over $z\in\mathbb R^n$. Its minimizer is unique and equals the average step:
--   $$z \text{ minimizes } L_\rho(x,\cdot,y)\iff z=\bar x+(1/\rho)\bar y.$$
--
--   This is why the central collector of consensus ADMM only has to average.
--
--   **Formalization Note** The book states the algorithm with the averaging formula (p. 49) and rewrites it with overlines (p. 50); the statement here is the underlying fact that this formula is the exact (and unique) minimizer of $L_\rho$ in $z$. The terms $f_i(x_i)$ are constants in $z$ and are kept as in $L_\rho$. The hypotheses $N\ge1$ and $\rho>0$ are implicit in the book.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), pp. 49–50, §7.1 (ADMM for (7.1) and its simplification z^{k+1} = x̄^{k+1} + (1/ρ)ȳ^k)

import Mathlib
import Definitions.Def_BoydADMM_Consensus_Model

open scoped BigOperators InnerProductSpace

namespace BoydADMM.Consensus

/-- §7.1, pp. 49–50: the consensus `z`-update, the minimization of
`L_ρ(x^{k+1}, z, y^k)` over `z ∈ ℝⁿ`, has the unique solution `z = x̄^{k+1} + (1/ρ) ȳ^k`. The
terms `f_i(x_i^{k+1})` of `L_ρ` do not depend on `z` and are kept. -/
theorem consensus_z_update_average {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : Fin N → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)) :
    (∀ z' : EuclideanSpace ℝ (Fin n),
        ∑ i, (f i (x i) + ⟪y i, x i - z⟫_ℝ + (ρ / 2) * ‖x i - z‖ ^ 2) ≤
          ∑ i, (f i (x i) + ⟪y i, x i - z'⟫_ℝ + (ρ / 2) * ‖x i - z'‖ ^ 2)) ↔
      z = avg x + (1 / ρ) • avg y := by sorry

end BoydADMM.Consensus
