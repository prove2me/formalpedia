-- Prove2me | Theorems.Thm_BoydADMM_Convergence_z_update_dual_feasible
-- name    : BoydADMM.Convergence.z_update_dual_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:53:27.850866+00:00
-- url     : https://prove2.me/theorems/fdd1c369-678f-49e7-80a0-5951cca69bd4
-- title:
--   §3.3 — $z^{k+1}$ and $y^{k+1}$ always satisfy (3.10): $0\in\partial g(z^{k+1})+B^Ty^{k+1}$
-- statement:
--   Let $f,g$ satisfy Assumption 1 (closed, proper, convex), let $\rho>0$, and let $(x^k,z^k,y^k)$ be any ADMM run (3.2)–(3.4) for problem (3.1). Then for every $k\ge0$,
--
--   $$
--   0\in\partial g(z^{k+1})+B^Ty^{k+1},
--   $$
--
--   that is, the pair $(z^{k+1},y^{k+1})$ satisfies the dual feasibility condition (3.10) at every iteration. Here $\partial g(z)$ is the subdifferential of $g$ at $z\in\operatorname{dom}g$: the set of $v$ with $g(z')\ge g(z)+v^T(z'-z)$ for all $z'\in\operatorname{dom}g$.
--
--   Consequently optimality of ADMM iterates reduces to the two remaining conditions, primal feasibility (3.8) and dual feasibility (3.9).
--
--   **Formalization Note** The statement is written as $-B^Ty^{k+1}\in\partial g(z^{k+1})$ with the published subdifferential `ShorNonsmooth.Subdiff.subdifferential` relative to $M=\operatorname{dom}g$, which is the convex-analysis subdifferential of the extended-valued $g$ at a point of its domain.
-- source:
--   Boyd et al., Found. Trends Mach. Learn. 3(1) (2011), §3.3, p. 18, (3.10)

import Mathlib
import Definitions.Def_BoydADMM_Convergence_Model
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential

namespace BoydADMM.Convergence

/-- §3.3, p. 18: `z^{k+1}` and `y^{k+1}` always satisfy (3.10),
`0 ∈ ∂g(z^{k+1}) + Bᵀy^{k+1}`, i.e. `−Bᵀy^{k+1} ∈ ∂g(z^{k+1})`, for every `k ≥ 0`. -/
theorem z_update_dual_feasible
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    -P.BTmul (y (k + 1)) ∈ ShorNonsmooth.Subdiff.subdifferential P.Cg P.g (z (k + 1)) := by sorry

end BoydADMM.Convergence
