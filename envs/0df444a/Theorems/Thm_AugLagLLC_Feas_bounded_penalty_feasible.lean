-- Prove2me | Theorems.Thm_AugLagLLC_Feas_bounded_penalty_feasible
-- name    : AugLagLLC.Feas.bounded_penalty_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:37:05.309005+00:00
-- url     : https://prove2.me/theorems/b56fce8b-3751-43fc-a66e-ff566465bd94
-- title:
--   Proof of Theorem 4.1, case (a), p. 6 — if {ρₖ} is bounded, every limit point is feasible for (2.1)
-- statement:
--   Consider problem (2.1) with continuously differentiable data and a run $\{x_k\}$ of Algorithm 3.1 with valid parameters. If the sequence of penalty parameters $\{\rho_k\}$ is bounded, then every limit point $x_*$ of $\{x_k\}$ is feasible:
--   $$x_*\in\Omega_1\cap\Omega_2,\quad\text{i.e. } h_1(x_*)=0,\ g_1(x_*)\le0,\ h_2(x_*)=0,\ g_2(x_*)\le0 .$$
--
--   This is the first assertion of Theorem 4.1, proved in case (a) of its proof from the vanishing of $\|h_1(x_k)\|$ and $\|\sigma_k\|$ and from $x_*\in\Omega_2$.
--
--   **Formalization Note** "Bounded" is `BddAbove (Set.range ρ)`; the penalty parameters are positive, so this is boundedness. The unused value $\rho_0$ cannot affect it. "Limit point" is `MapClusterPt`.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, p. 6, proof of Theorem 4.1, case (a), and first sentence of Theorem 4.1

import Mathlib
import Definitions.Def_AugLagLLC_Feas_Setting

open Filter
open scoped Topology

namespace AugLagLLC.Feas
theorem bounded_penalty_feasible {n m1 p1 m2 p2 : ℕ} (P : Problem n m1 p1 m2 p2) (hP : P.IsC1)
    {τ γ ρ1 : ℝ} {lamMin lamMax : Fin m1 → ℝ} {muMax : Fin p1 → ℝ} {ε : ℕ → ℝ}
    (hpar : ValidParams τ γ ρ1 lamMin lamMax muMax ε)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {ρ : ℕ → ℝ} {lamBar : ℕ → Fin m1 → ℝ}
    {muBar : ℕ → Fin p1 → ℝ} {v : ℕ → Fin m2 → ℝ} {u : ℕ → Fin p2 → ℝ}
    (hrun : IsRun P τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u)
    (hbdd : BddAbove (Set.range ρ))
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : MapClusterPt xs atTop x) :
    xs ∈ P.Omega1 ∩ P.Omega2 := by sorry
end AugLagLLC.Feas
