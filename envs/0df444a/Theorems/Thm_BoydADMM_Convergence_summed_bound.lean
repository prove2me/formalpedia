-- Prove2me | Theorems.Thm_BoydADMM_Convergence_summed_bound
-- name    : BoydADMM.Convergence.summed_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:06.335659+00:00
-- url     : https://prove2.me/theorems/93f31c60-bf74-480c-80b6-2a589112a2e4
-- title:
--   Appendix A, p. 107 — $\rho\sum(\|r^{k+1}\|_2^2+\|B(z^{k+1}-z^k)\|_2^2)$ is bounded, so $r^k\to0$ and $B(z^{k+1}-z^k)\to0$
-- statement:
--   Under Assumptions 1 and 2, with $\rho>0$, a saddle point $(x^\star,z^\star,y^\star)$ of $L_0$ and any ADMM run, let $V^k=(1/\rho)\|y^k-y^\star\|_2^2+\rho\|B(z^k-z^\star)\|_2^2$ and $r^k=Ax^k+Bz^k-c$. Then
--
--   $$
--   \rho\sum_{k=1}^{\infty}\Bigl(\|r^{k+1}\|_2^2+\|B(z^{k+1}-z^k)\|_2^2\Bigr)\le V^1,
--   $$
--
--   and consequently $r^k\to0$ and $B(z^{k+1}-z^k)\to0$ as $k\to\infty$.
--
--   The vanishing of $B(z^{k+1}-z^k)$ gives, after multiplication by $\rho A^T$, the convergence of the dual residual to zero.
--
--   **Formalization Note** The book writes the sum from $k=0$ bounded by $V^0$, obtained by iterating (A.1); since (A.1) is proved only for $k\ge1$ (see `ineq_A1`), we state the sum from $k=1$ bounded by $V^1$, which yields the same limits. The infinite sum is stated as the bound on every partial sum, $\rho\sum_{j=0}^{N-1}(\|r^{j+2}\|^2+\|B(z^{j+2}-z^{j+1})\|^2)\le V^1$ for all $N$, which for nonnegative terms is equivalent and avoids Lean's convention for non-summable series.
-- source:
--   Boyd et al., Found. Trends Mach. Learn. 3(1) (2011), Appendix A, p. 107

import Mathlib
import Definitions.Def_BoydADMM_Convergence_Model

namespace BoydADMM.Convergence

/-- p. 107: iterating (A.1) gives
`ρ ∑_{k ≥ 1} (‖r^{k+1}‖₂² + ‖B(z^{k+1} − z^k)‖₂²) ≤ V^1` (every partial sum is bounded by
`V^1`), which implies `r^k → 0` and `B(z^{k+1} − z^k) → 0`. -/
theorem summed_bound
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) :
    (∀ N : ℕ, ρ * ∑ j ∈ Finset.range N,
        (‖P.resid (x (j + 2)) (z (j + 2))‖ ^ 2 + ‖P.Bmul (z (j + 2) - z (j + 1))‖ ^ 2) ≤
      P.lyapunov ρ zs ys (z 1) (y 1)) ∧
    Filter.Tendsto (fun k => P.resid (x k) (z k)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => P.Bmul (z (k + 1) - z k)) Filter.atTop (nhds 0) := by sorry

end BoydADMM.Convergence
