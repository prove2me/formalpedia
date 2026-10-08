-- Prove2me | Theorems.Thm_AugLagLLC_Feas_limit_mem_omega2
-- name    : AugLagLLC.Feas.limit_mem_omega2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:37:16.066985+00:00
-- url     : https://prove2.me/theorems/b6a7c40f-663d-4a8d-bdf8-38d17298731f
-- title:
--   Proof of Theorem 4.1, p. 6 — every limit point of a run of Algorithm 3.1 lies in Ω₂
-- statement:
--   Consider problem (2.1) with continuously differentiable data and a run $\{x_k\}$ of Algorithm 3.1 (with valid parameters, and Step 2 never failing). Let $x_*$ be a limit point of $\{x_k\}$. Then $x_*$ satisfies the lower-level constraints:
--   $$h_2(x_*)=0,\qquad g_2(x_*)\le 0,\qquad\text{i.e. } x_*\in\Omega_2 .$$
--
--   This is the first step of the proof of Theorem 4.1: the subproblem tolerances (3.2) and (3.4) vanish because $\varepsilon_k\to0$. It is used in both cases of the theorem.
--
--   **Formalization Note** "Limit point" is `MapClusterPt xs atTop x` (a cluster point of the whole sequence, including $x_0$, which does not change the set of limit points). Continuity of $h_2,g_2$ comes from the standing $C^1$ hypothesis.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, p. 6, proof of Theorem 4.1, first paragraph

import Mathlib
import Definitions.Def_AugLagLLC_Feas_Setting

open Filter
open scoped Topology

namespace AugLagLLC.Feas
theorem limit_mem_omega2 {n m1 p1 m2 p2 : ℕ} (P : Problem n m1 p1 m2 p2) (hP : P.IsC1)
    {τ γ ρ1 : ℝ} {lamMin lamMax : Fin m1 → ℝ} {muMax : Fin p1 → ℝ} {ε : ℕ → ℝ}
    (hpar : ValidParams τ γ ρ1 lamMin lamMax muMax ε)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {ρ : ℕ → ℝ} {lamBar : ℕ → Fin m1 → ℝ}
    {muBar : ℕ → Fin p1 → ℝ} {v : ℕ → Fin m2 → ℝ} {u : ℕ → Fin p2 → ℝ}
    (hrun : IsRun P τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : MapClusterPt xs atTop x) :
    xs ∈ P.Omega2 := by sorry
end AugLagLLC.Feas
