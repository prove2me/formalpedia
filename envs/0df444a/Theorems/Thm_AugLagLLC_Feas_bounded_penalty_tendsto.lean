-- Prove2me | Theorems.Thm_AugLagLLC_Feas_bounded_penalty_tendsto
-- name    : AugLagLLC.Feas.bounded_penalty_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:37:07.10053+00:00
-- url     : https://prove2.me/theorems/a2925a38-fb75-407a-af7c-7674beb1e0c7
-- title:
--   Proof of Theorem 4.1, case (a), p. 6 — bounded {ρₖ} gives ‖h₁(xₖ)‖ → 0 and ‖σₖ‖ → 0
-- statement:
--   Let $\{x_k\}$ be a run of Algorithm 3.1 with valid parameters, and suppose the sequence of penalty parameters $\{\rho_k\}$ is bounded. Then
--   $$\lim_{k\to\infty}\|h_1(x_k)\|_\infty=0\qquad\text{and}\qquad\lim_{k\to\infty}\|\sigma_k\|_\infty=0,$$
--   where $[\sigma_k]_i=\max\{[g_1(x_k)]_i,-[\bar\mu_k]_i/\rho_k\}$ is the combined infeasibility–complementarity measure of Step 3.
--
--   This is case (a) of the proof of Theorem 4.1: a bounded penalty sequence is updated only finitely often, after which the Step 4 test holds at every iteration.
--
--   **Formalization Note** The paper's norm is arbitrary; this statement uses the sup norm, the norm of the Step 4 test, and the limits are equivalent in any norm. $\sigma_0$ is the Step 1 value $\max\{0,[g_1(x_0)]_i\}$, which does not affect the limit. No differentiability hypothesis is needed for this step.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, p. 6, proof of Theorem 4.1, case (a)

import Mathlib
import Definitions.Def_AugLagLLC_Feas_Setting

open Filter
open scoped Topology

namespace AugLagLLC.Feas
theorem bounded_penalty_tendsto {n m1 p1 m2 p2 : ℕ} (P : Problem n m1 p1 m2 p2)
    {τ γ ρ1 : ℝ} {lamMin lamMax : Fin m1 → ℝ} {muMax : Fin p1 → ℝ} {ε : ℕ → ℝ}
    (hpar : ValidParams τ γ ρ1 lamMin lamMax muMax ε)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {ρ : ℕ → ℝ} {lamBar : ℕ → Fin m1 → ℝ}
    {muBar : ℕ → Fin p1 → ℝ} {v : ℕ → Fin m2 → ℝ} {u : ℕ → Fin p2 → ℝ}
    (hrun : IsRun P τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u)
    (hbdd : BddAbove (Set.range ρ)) :
    Tendsto (fun k => ‖h1vec P (x k)‖) atTop (𝓝 0) ∧
    Tendsto (fun k => ‖sigma P x ρ muBar k‖) atTop (𝓝 0) := by sorry
end AugLagLLC.Feas
