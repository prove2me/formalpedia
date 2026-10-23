-- Prove2me | Theorems.Thm_BoydADMM2011_admm_convergence_with_dual_faithful
-- name    : BoydADMM2011.admm_convergence_with_dual_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T03:23:13.72923+00:00
-- url     : https://prove2.me/theorems/32ee608b-0b29-47a6-beeb-eb8e79b08d32
-- title:
--   §3.2.1 ADMM convergence, all three bullets (residual, objective and dual variable convergence)
-- statement:
--   Consider problem (3.1), minimize $f(x)+g(z)$ subject to $Ax+Bz=c$ with $x\in\mathbb{R}^n$, $z\in\mathbb{R}^m$, $A\in\mathbb{R}^{p\times n}$, $B\in\mathbb{R}^{p\times m}$, $c\in\mathbb{R}^p$, and optimal value $p^\star=\inf\{f(x)+g(z)\mid Ax+Bz=c\}$. Assume $f$ and $g$ are closed, proper and convex, and that the unaugmented Lagrangian $L_0$ has a saddle point $(x^\star,z^\star,y^\star)$. Let $\rho>0$ and let $(x^k,z^k,y^k)$ be any run of the ADMM iterations (3.2)–(3.4). Then, as $k\to\infty$,
--
--   $$r^k = Ax^k+Bz^k-c \to 0,\qquad f(x^k)+g(z^k)\to p^\star,\qquad y^k\to y^\infty \text{ for some dual optimal point } y^\infty .$$
--
--   That is:
--
--   1. residual convergence, $r^k\to 0$;
--   2. objective convergence, $f(x^k)+g(z^k)\to p^\star$;
--   3. dual variable convergence, $y^k\to y^\infty$ with $y^\infty$ dual optimal.
--
--   This is the convergence result of §3.2.1 (p. 17) of Boyd et al. with all three of its bullets. The existing theorem BoydADMM.Convergence.admm_convergence proves parts 1 and 2 (and the dual residual limit) but not part 3.
--
--   **Formalization Note** Under a saddle point, the dual optimal points are exactly the $y$ for which $(x^\star,z^\star,y)$ is again a saddle point of $L_0$ (saddle points of a convex–concave Lagrangian form a product set), so "dual optimal" is encoded as `P.IsSaddlePoint xs zs yinf`. Extended-real $f,g$ are encoded by their effective domains, as in the existing theorem.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), doi:10.1561/2200000016, §3.2.1, p. 17

import Mathlib
import Definitions.Def_BoydADMM_Convergence_Model

open BoydADMM.Convergence

theorem BoydADMM2011.admm_convergence_with_dual_faithful
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) :
    Filter.Tendsto (fun k => P.resid (x k) (z k)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => P.f (x k) + P.g (z k)) Filter.atTop (nhds P.optVal) ∧
    ∃ yinf : EuclideanSpace ℝ (Fin p), P.IsSaddlePoint xs zs yinf ∧
      Filter.Tendsto y Filter.atTop (nhds yinf) := by sorry
