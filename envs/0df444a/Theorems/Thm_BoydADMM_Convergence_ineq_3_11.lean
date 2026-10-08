-- Prove2me | Theorems.Thm_BoydADMM_Convergence_ineq_3_11
-- name    : BoydADMM.Convergence.ineq_3_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:53:49.77236+00:00
-- url     : https://prove2.me/theorems/f72f01c4-e43c-42b4-8e3e-be42ebc08230
-- title:
--   (3.11) — $f(x^k)+g(z^k)-p^\star\le-(y^k)^Tr^k+(x^k-x^\star)^Ts^k$
-- statement:
--   Under Assumptions 1 and 2, with $\rho>0$, a saddle point $(x^\star,z^\star,y^\star)$ of $L_0$ and any ADMM run, for every iteration $k\ge1$
--
--   $$
--   f(x^k)+g(z^k)-p^\star\le-(y^k)^Tr^k+(x^k-x^\star)^Ts^k,
--   $$
--
--   where $r^k=Ax^k+Bz^k-c$ is the primal residual and $s^k=\rho A^TB(z^k-z^{k-1})$ the dual residual.
--
--   The bound shows that small residuals force small objective suboptimality; it underlies the stopping criterion of §3.3.1.
--
--   **Formalization Note** Stated at index $k+1$ for $k\ge0$ (as on p. 107), since $x^0$ and $s^0$ are not defined by the method. $p^\star$ is the infimum `optVal`. The book derives (3.11) from (A.2) via the identity printed as "$-r^{k+1}+B(z^{k+1}-z^k)=-A(x^{k+1}-x^\star)$"; the intended identity, forced by (A.2) and $Ax^\star+Bz^\star=c$, is $-r^{k+1}+B(z^{k+1}-z^\star)=-A(x^{k+1}-x^\star)$. The statement of (3.11) itself is unaffected.
-- source:
--   Boyd et al., Found. Trends Mach. Learn. 3(1) (2011), §3.3.1, p. 19, (3.11); derived on p. 107

import Mathlib
import Definitions.Def_BoydADMM_Convergence_Model

namespace BoydADMM.Convergence

/-- (3.11), p. 19 (stated at index `k + 1` on p. 107): for every `k ≥ 0`,
`f(x^{k+1}) + g(z^{k+1}) − p⋆ ≤ −(y^{k+1})ᵀr^{k+1} + (x^{k+1} − x⋆)ᵀs^{k+1}`,
with `s^{k+1} = ρAᵀB(z^{k+1} − z^k)`. -/
theorem ineq_3_11
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    P.f (x (k + 1)) + P.g (z (k + 1)) - P.optVal ≤
      -inner ℝ (y (k + 1)) (P.resid (x (k + 1)) (z (k + 1)))
        + inner ℝ (x (k + 1) - xs) (P.dualResid ρ (z k) (z (k + 1))) := by sorry

end BoydADMM.Convergence
