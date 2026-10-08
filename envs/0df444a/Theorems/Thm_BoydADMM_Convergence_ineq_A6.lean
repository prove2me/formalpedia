-- Prove2me | Theorems.Thm_BoydADMM_Convergence_ineq_A6
-- name    : BoydADMM.Convergence.ineq_A6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:01.913527+00:00
-- url     : https://prove2.me/theorems/d5f97d0f-aa86-4af8-8ccd-15433ec78a30
-- title:
--   (A.6) — $V^k-V^{k+1}\ge\rho\|r^{k+1}-B(z^{k+1}-z^k)\|_2^2$
-- statement:
--   Under Assumptions 1 and 2, with $\rho>0$, a saddle point $(x^\star,z^\star,y^\star)$ of $L_0$ and any ADMM run, let
--
--   $$
--   V^k=\frac1\rho\|y^k-y^\star\|_2^2+\rho\|B(z^k-z^\star)\|_2^2 .
--   $$
--
--   Then for every $k\ge0$,
--
--   $$
--   V^k-V^{k+1}\ge\rho\|r^{k+1}-B(z^{k+1}-z^k)\|_2^2,
--   $$
--
--   where $r^{k+1}=Ax^{k+1}+Bz^{k+1}-c$. In particular $V^{k+1}\le V^k$: the Lyapunov function does not increase.
-- source:
--   Boyd et al., Found. Trends Mach. Learn. 3(1) (2011), Appendix A, p. 110, (A.6)

import Mathlib
import Definitions.Def_BoydADMM_Convergence_Model

namespace BoydADMM.Convergence

/-- (A.6), p. 110: `V^k − V^{k+1} ≥ ρ‖r^{k+1} − B(z^{k+1} − z^k)‖₂²` for every `k ≥ 0`,
with `V^k = (1/ρ)‖y^k − y⋆‖₂² + ρ‖B(z^k − z⋆)‖₂²`. -/
theorem ineq_A6
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    P.lyapunov ρ zs ys (z k) (y k) - P.lyapunov ρ zs ys (z (k + 1)) (y (k + 1)) ≥
      ρ * ‖P.resid (x (k + 1)) (z (k + 1)) - P.Bmul (z (k + 1) - z k)‖ ^ 2 := by sorry

end BoydADMM.Convergence
