-- Prove2me | Theorems.Thm_BoydADMM_Convergence_admm_convergence
-- name    : BoydADMM.Convergence.admm_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:16.357831+00:00
-- url     : https://prove2.me/theorems/0fe48803-2d9b-45b0-bbab-ff109616c5a3
-- title:
--   §3.2.1 — under Assumptions 1–2, ADMM residuals $r^k,s^k\to0$ and $f(x^k)+g(z^k)\to p^\star$
-- statement:
--   Consider problem (3.1), minimize $f(x)+g(z)$ subject to $Ax+Bz=c$, with optimal value $p^\star$. Assume
--
--   1. (Assumption 1) $f$ and $g$ are closed, proper and convex;
--   2. (Assumption 2) the Lagrangian $L_0$ has a saddle point $(x^\star,z^\star,y^\star)$;
--
--   and let $\rho>0$. Then every ADMM run $(x^k,z^k,y^k)$, i.e. any sequences satisfying (3.2)–(3.4), satisfies, as $k\to\infty$,
--
--   $$
--   r^k=Ax^k+Bz^k-c\to0,\qquad f(x^k)+g(z^k)\to p^\star,\qquad s^k=\rho A^TB(z^k-z^{k-1})\to0 .
--   $$
--
--   These are residual convergence (the iterates approach feasibility), objective convergence (the objective approaches the optimal value) and convergence of the dual residual. No rank condition on $A$ or $B$ is assumed, and the iterates $x^k,z^k$ themselves need not converge.
--
--   **Formalization Note** The run is any triple of sequences satisfying (3.2)–(3.4) exactly; it is never constructed (the book's claim that Assumption 1 alone makes the subproblems solvable is false). $p^\star$ is the infimum `optVal`, not $f(x^\star)+g(z^\star)$ by definition. The dual residual sequence is written as $s^{k+1}=\rho A^TB(z^{k+1}-z^k)$, a shift that does not change the limit; the first term of each sequence (which involves the unused $x^0$) does not affect the limits either. The book also lists dual variable convergence $y^k\to y^\star$ in §3.2.1; Appendix A does not prove it and it is not part of this statement.
-- source:
--   Boyd et al., Found. Trends Mach. Learn. 3(1) (2011), §3.2.1, p. 17; Appendix A, p. 106

import Mathlib
import Definitions.Def_BoydADMM_Convergence_Model

namespace BoydADMM.Convergence

/-- §3.2.1, p. 17, as proved in Appendix A (p. 106): under Assumptions 1 and 2, every ADMM
run satisfies residual convergence `r^k → 0`, objective convergence `f(x^k) + g(z^k) → p⋆`, and
dual residual convergence `s^k = ρAᵀB(z^k − z^{k−1}) → 0`. -/
theorem admm_convergence
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) :
    Filter.Tendsto (fun k => P.resid (x k) (z k)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => P.f (x k) + P.g (z k)) Filter.atTop (nhds P.optVal) ∧
    Filter.Tendsto (fun k => P.dualResid ρ (z k) (z (k + 1))) Filter.atTop (nhds 0) := by sorry

end BoydADMM.Convergence
