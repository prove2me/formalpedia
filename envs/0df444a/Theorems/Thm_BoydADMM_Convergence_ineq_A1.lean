-- Prove2me | Theorems.Thm_BoydADMM_Convergence_ineq_A1
-- name    : BoydADMM.Convergence.ineq_A1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:01.147558+00:00
-- url     : https://prove2.me/theorems/788beb59-f60a-4a42-9210-2852b8cbbe8f
-- title:
--   (A.1) — $V^{k+1}\le V^k-\rho\|r^{k+1}\|_2^2-\rho\|B(z^{k+1}-z^k)\|_2^2$ for $k\ge1$
-- statement:
--   Under Assumptions 1 and 2, with $\rho>0$, a saddle point $(x^\star,z^\star,y^\star)$ of $L_0$ and any ADMM run, let $V^k=(1/\rho)\|y^k-y^\star\|_2^2+\rho\|B(z^k-z^\star)\|_2^2$ and $r^k=Ax^k+Bz^k-c$. Then for every $k\ge1$,
--
--   $$
--   V^{k+1}\le V^k-\rho\|r^{k+1}\|_2^2-\rho\|B(z^{k+1}-z^k)\|_2^2 .
--   $$
--
--   This is the first key inequality of Appendix A: $V^k$ decreases by an amount controlled by the primal residual and the change in $Bz$.
--
--   **Formalization Note** The book states (A.1) without an index range, but its proof uses the monotonicity step, which needs $z^k$ to be a $z$-update, so it is proved for $k\ge1$; for $k=0$ and an arbitrary $z^0$ the inequality can fail. We state $k\ge1$, written with $k+1$, $k+2$ in place of $k$, $k+1$.
-- source:
--   Boyd et al., Found. Trends Mach. Learn. 3(1) (2011), Appendix A, p. 107, (A.1); proof pp. 109–110

import Mathlib
import Definitions.Def_BoydADMM_Convergence_Model

namespace BoydADMM.Convergence

/-- (A.1), p. 107: `V^{k+1} ≤ V^k − ρ‖r^{k+1}‖₂² − ρ‖B(z^{k+1} − z^k)‖₂²` for every book
index `k ≥ 1` (here written with `k + 1` in place of the book's `k`). -/
theorem ineq_A1
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    P.lyapunov ρ zs ys (z (k + 2)) (y (k + 2)) ≤
      P.lyapunov ρ zs ys (z (k + 1)) (y (k + 1))
        - ρ * ‖P.resid (x (k + 2)) (z (k + 2))‖ ^ 2
        - ρ * ‖P.Bmul (z (k + 2) - z (k + 1))‖ ^ 2 := by sorry

end BoydADMM.Convergence
