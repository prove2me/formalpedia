-- Prove2me | Theorems.Thm_BoydADMM_Convergence_ineq_A3
-- name    : BoydADMM.Convergence.ineq_A3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:53:39.519928+00:00
-- url     : https://prove2.me/theorems/de92c5e6-53d7-4b8f-b35d-0272c5a4cf82
-- title:
--   (A.3) — $p^\star-p^{k+1}\le y^{\star T}r^{k+1}$
-- statement:
--   Let $f,g$ satisfy Assumption 1, let $\rho>0$, let $(x^\star,z^\star,y^\star)$ be a saddle point of the Lagrangian $L_0$ (Assumption 2), and let $(x^k,z^k,y^k)$ be any ADMM run. Write $p^k=f(x^k)+g(z^k)$ and $r^k=Ax^k+Bz^k-c$, and let $p^\star$ be the optimal value of (3.1). Then for every $k\ge0$,
--
--   $$
--   p^\star-p^{k+1}\le y^{\star T}r^{k+1}.
--   $$
--
--   This is the third key inequality of the convergence proof: since $r^k\to0$, it bounds the objective from below in the limit.
--
--   **Formalization Note** $p^\star$ is the infimum `optVal` over feasible points of the domains, not $f(x^\star)+g(z^\star)$ by definition.
-- source:
--   Boyd et al., Found. Trends Mach. Learn. 3(1) (2011), Appendix A, p. 107, (A.3); proof p. 108

import Mathlib
import Definitions.Def_BoydADMM_Convergence_Model

namespace BoydADMM.Convergence

/-- (A.3), p. 107: `p⋆ − p^{k+1} ≤ y⋆ᵀr^{k+1}` for every `k ≥ 0`, where
`p^{k+1} = f(x^{k+1}) + g(z^{k+1})` and `r^{k+1} = Ax^{k+1} + Bz^{k+1} − c`. -/
theorem ineq_A3
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    P.optVal - (P.f (x (k + 1)) + P.g (z (k + 1))) ≤
      inner ℝ ys (P.resid (x (k + 1)) (z (k + 1))) := by sorry

end BoydADMM.Convergence
