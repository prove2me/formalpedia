-- Prove2me | Theorems.Thm_BoydADMM_Consensus_regularized_z_update_prox
-- name    : BoydADMM.Consensus.regularized_z_update_prox
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:06:15.772103+00:00
-- url     : https://prove2.me/theorems/bd66b017-6b3c-4163-be01-b8bb9ff7f03c
-- title:
--   (7.4): the regularized consensus $z$-update is averaging followed by a proximal step with weight $N\rho$
-- statement:
--   Let $N\ge1$, $\rho>0$, and let $g:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be any regularizer. Fix $x_1,\dots,x_N$ (standing for $x_i^{k+1}$) and $y_1,\dots,y_N$ (standing for $y_i^k$). Then a point $z\in\operatorname{dom} g$ minimizes the $z$-update objective (7.4)
--   $$g(z)+\sum_{i=1}^N\big(-y_i^{T}z+(\rho/2)\|x_i-z\|_2^2\big)$$
--   over $\operatorname{dom} g$ if and only if it minimizes the proximal objective
--   $$g(z)+(N\rho/2)\,\|z-\bar x-(1/\rho)\bar y\|_2^2$$
--   over $\operatorname{dom} g$.
--
--   So the central collector first averages and then applies the proximal operator of $g$ with parameter $N\rho$.
--
--   **Formalization Note** Each extended-real-valued function $\varphi:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ of the book is encoded by its effective domain $\operatorname{dom}\varphi$ (a set) and its finite values on it (a real function); a minimization of a sum containing $\varphi$ is a minimization over $\operatorname{dom}\varphi$. No convexity of $g$ is needed: the two objectives differ by a constant independent of $z$. The minimizer sets are compared, not a selected minimizer.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 52, §7.1.1, (7.4) and the averaging-plus-proximal form of the z-update

import Mathlib
import Definitions.Def_BoydADMM_Consensus_Model

open scoped BigOperators InnerProductSpace

namespace BoydADMM.Consensus

/-- §7.1.1, p. 52: for a regularizer `g` with effective domain `Cg`, the `z`-update (7.4)
`argmin_z (g(z) + ∑_i (−y_i^{kT} z + (ρ/2)‖x_i^{k+1} − z‖²))` has exactly the same
minimizers as the averaging-then-proximal step
`argmin_z (g(z) + (Nρ/2)‖z − x̄^{k+1} − (1/ρ)ȳ^k‖²)`. Here `x`, `y` stand for `x^{k+1}`, `y^k`. -/
theorem regularized_z_update_prox {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (Cg : Set (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : Fin N → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)) :
    (z ∈ Cg ∧ ∀ z' ∈ Cg,
        g z + ∑ i, (-⟪y i, z⟫_ℝ + (ρ / 2) * ‖x i - z‖ ^ 2) ≤
          g z' + ∑ i, (-⟪y i, z'⟫_ℝ + (ρ / 2) * ‖x i - z'‖ ^ 2)) ↔
      (z ∈ Cg ∧ ∀ z' ∈ Cg,
        g z + ((N : ℝ) * ρ / 2) * ‖z - avg x - (1 / ρ) • avg y‖ ^ 2 ≤
          g z' + ((N : ℝ) * ρ / 2) * ‖z' - avg x - (1 / ρ) • avg y‖ ^ 2) := by sorry

end BoydADMM.Consensus
