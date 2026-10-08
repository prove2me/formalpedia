-- Prove2me | Theorems.Thm_BoydADMM_Convergence_ineq_A2
-- name    : BoydADMM.Convergence.ineq_A2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:53:51.957443+00:00
-- url     : https://prove2.me/theorems/467ac7dd-b0a1-43be-9c38-1ece4ba0ad9e
-- title:
--   (A.2) — $p^{k+1}-p^\star\le-(y^{k+1})^Tr^{k+1}-\rho(B(z^{k+1}-z^k))^T(-r^{k+1}+B(z^{k+1}-z^\star))$
-- statement:
--   Under Assumptions 1 and 2, with $\rho>0$, a saddle point $(x^\star,z^\star,y^\star)$ of $L_0$ and any ADMM run $(x^k,z^k,y^k)$, for every $k\ge0$
--
--   $$
--   p^{k+1}-p^\star\le-(y^{k+1})^Tr^{k+1}-\rho\bigl(B(z^{k+1}-z^k)\bigr)^T\bigl(-r^{k+1}+B(z^{k+1}-z^\star)\bigr),
--   $$
--
--   where $p^k=f(x^k)+g(z^k)$, $r^k=Ax^k+Bz^k-c$ and $p^\star$ is the optimal value of (3.1).
--
--   This is the second key inequality of Appendix A; it bounds the objective from above by quantities that vanish along the iteration.
--
--   **Formalization Note** $p^\star$ is the infimum `optVal`.
-- source:
--   Boyd et al., Found. Trends Mach. Learn. 3(1) (2011), Appendix A, p. 107, (A.2); proof p. 108

import Mathlib
import Definitions.Def_BoydADMM_Convergence_Model

namespace BoydADMM.Convergence

/-- (A.2), p. 107: for every `k ≥ 0`,
`p^{k+1} − p⋆ ≤ −(y^{k+1})ᵀr^{k+1} − ρ(B(z^{k+1} − z^k))ᵀ(−r^{k+1} + B(z^{k+1} − z⋆))`. -/
theorem ineq_A2
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    P.f (x (k + 1)) + P.g (z (k + 1)) - P.optVal ≤
      -inner ℝ (y (k + 1)) (P.resid (x (k + 1)) (z (k + 1)))
        - ρ * inner ℝ (P.Bmul (z (k + 1) - z k))
            (-P.resid (x (k + 1)) (z (k + 1)) + P.Bmul (z (k + 1) - zs)) := by sorry

end BoydADMM.Convergence
