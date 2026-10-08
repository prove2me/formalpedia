-- Prove2me | Theorems.Thm_AugLagLLC_Feas_eq_4_2
-- name    : AugLagLLC.Feas.eq_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:36:59.669579+00:00
-- url     : https://prove2.me/theorems/e709d08b-c24b-4392-8d32-3870af548b98
-- title:
--   (4.2), proof of Theorem 4.1, p. 6 — the explicit gradient form of (3.1): ‖δₖ‖ ≤ εₖ and δₖ → 0
-- statement:
--   Consider problem (2.1) with continuously differentiable data and a run of Algorithm 3.1 with valid parameters, iterates $x_k$, penalty parameters $\rho_k$, safeguarded estimates $\bar\lambda_k,\bar\mu_k$ and lower-level multipliers $v_k,u_k$. For every outer iteration $k\ge1$ define
--   $$\delta_k=\nabla f(x_k)+\sum_{i=1}^{m_1}\big([\bar\lambda_k]_i+\rho_k[h_1(x_k)]_i\big)\nabla[h_1(x_k)]_i+\sum_{i=1}^{p_1}\max\{0,[\bar\mu_k]_i+\rho_k[g_1(x_k)]_i\}\nabla[g_1(x_k)]_i+\sum_{i=1}^{m_2}[v_k]_i\nabla[h_2(x_k)]_i+\sum_{j=1}^{p_2}[u_k]_j\nabla[g_2(x_k)]_j .$$
--   Then
--   $$\|\delta_k\|\le\varepsilon_k\quad(k\ge1)\qquad\text{and}\qquad\lim_{k\to\infty}\|\delta_k\|=0 .$$
--
--   The vector $\delta_k$ is the residual of (3.1) once $\nabla L$ is computed from (2.2); this identity is the starting point of case (b) of the proof of Theorem 4.1.
--
--   **Formalization Note** $\nabla L$ in the run is the true gradient of the defined function (2.2); the explicit form above is what has to be computed, using $\rho_k>0$ and the differentiability of $t\mapsto(t)_+^2$. The norm is the Euclidean norm of $\mathbb R^n$. The paper states the limit along the subsequence $K$; the statement here is along the whole sequence, which is stronger and equally immediate from $\varepsilon_k\to0$.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, p. 6, proof of Theorem 4.1, case (b), (4.2)

import Mathlib
import Definitions.Def_AugLagLLC_Feas_Setting

open Filter
open scoped Topology

namespace AugLagLLC.Feas
theorem eq_4_2 {n m1 p1 m2 p2 : ℕ} (P : Problem n m1 p1 m2 p2) (hP : P.IsC1)
    {τ γ ρ1 : ℝ} {lamMin lamMax : Fin m1 → ℝ} {muMax : Fin p1 → ℝ} {ε : ℕ → ℝ}
    (hpar : ValidParams τ γ ρ1 lamMin lamMax muMax ε)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {ρ : ℕ → ℝ} {lamBar : ℕ → Fin m1 → ℝ}
    {muBar : ℕ → Fin p1 → ℝ} {v : ℕ → Fin m2 → ℝ} {u : ℕ → Fin p2 → ℝ}
    (hrun : IsRun P τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u) :
    let δ : ℕ → EuclideanSpace ℝ (Fin n) := fun k =>
      gradient P.f (x k)
        + ∑ i, (lamBar k i + ρ k * P.h1 i (x k)) • gradient (P.h1 i) (x k)
        + ∑ i, max 0 (muBar k i + ρ k * P.g1 i (x k)) • gradient (P.g1 i) (x k)
        + ∑ i, v k i • gradient (P.h2 i) (x k)
        + ∑ j, u k j • gradient (P.g2 j) (x k)
    (∀ k, 1 ≤ k → ‖δ k‖ ≤ ε k) ∧ Tendsto (fun k => ‖δ k‖) atTop (𝓝 0) := by sorry
end AugLagLLC.Feas
