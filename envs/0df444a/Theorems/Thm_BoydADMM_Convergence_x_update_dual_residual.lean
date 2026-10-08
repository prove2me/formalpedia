-- Prove2me | Theorems.Thm_BoydADMM_Convergence_x_update_dual_residual
-- name    : BoydADMM.Convergence.x_update_dual_residual
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:53:41.948247+00:00
-- url     : https://prove2.me/theorems/d0673d4b-697e-4f43-961a-60a74392fd8b
-- title:
--   §3.3 — $\rho A^TB(z^{k+1}-z^k)\in\partial f(x^{k+1})+A^Ty^{k+1}$
-- statement:
--   Let $f,g$ satisfy Assumption 1, let $\rho>0$, and let $(x^k,z^k,y^k)$ be any ADMM run (3.2)–(3.4). Then for every $k\ge0$,
--
--   $$
--   \rho A^TB(z^{k+1}-z^k)\in\partial f(x^{k+1})+A^Ty^{k+1}.
--   $$
--
--   Thus the **dual residual** $s^{k+1}=\rho A^TB(z^{k+1}-z^k)$ measures the violation of the dual feasibility condition (3.9), $0\in\partial f(x^\star)+A^Ty^\star$, at iteration $k+1$. Here $\partial f(x)$ is the subdifferential of $f$ at $x\in\operatorname{dom}f$.
--
--   **Formalization Note** Written as $s^{k+1}-A^Ty^{k+1}\in\partial f(x^{k+1})$ with `ShorNonsmooth.Subdiff.subdifferential` relative to $M=\operatorname{dom}f$.
-- source:
--   Boyd et al., Found. Trends Mach. Learn. 3(1) (2011), §3.3, p. 18

import Mathlib
import Definitions.Def_BoydADMM_Convergence_Model
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential

namespace BoydADMM.Convergence

/-- §3.3, p. 18: `ρAᵀB(z^{k+1} − z^k) ∈ ∂f(x^{k+1}) + Aᵀy^{k+1}`, i.e.
`s^{k+1} − Aᵀy^{k+1} ∈ ∂f(x^{k+1})`, for every `k ≥ 0`. -/
theorem x_update_dual_residual
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    P.dualResid ρ (z k) (z (k + 1)) - P.ATmul (y (k + 1)) ∈
      ShorNonsmooth.Subdiff.subdifferential P.Cf P.f (x (k + 1)) := by sorry

end BoydADMM.Convergence
