-- Prove2me | Theorems.Thm_AugLagLLC_Feas_Supplement_theorem_5_5
-- name    : AugLagLLC.Feas.Supplement.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:55:26.272126+00:00
-- url     : https://prove2.me/theorems/1db44204-013d-4f2b-99b5-f4c0caedd486
-- title:
--   Theorem 5.5 (corrected: positive τ and regularity (R)) — bounded penalties with general lower-level constraints
-- statement:
--   Consider the nonlinear program (2.1), minimize $f(x)$ on $\mathbb R^n$ subject to $h_1(x)=0$, $g_1(x)\le0$, $h_2(x)=0$ and $g_2(x)\le0$. All data are continuously differentiable. Let $x_k,\rho_k,\bar\lambda_k,\bar\mu_k,v_k,u_k$ form a run of Algorithm 3.1 with the projection safeguards of §5.2 and parameters $0<\tau<1$, $\gamma>1$ and $\rho_1>0$. The tolerance sequence $\varepsilon_k$ is nonnegative and tends to zero. The three subproblem tolerances of (3.1)–(3.4) remain separate.
--
--   Assume the whole sequence $x_k$ converges to a feasible point $x_*$ (Assumptions 7–8), LICQ holds for all equality gradients and active inequality gradients at $x_*$ (Assumption 9), and all data are twice continuously differentiable near $x_*$ (Assumption 10). Let $(\lambda_*,\mu_*,v_*,u_*)$ be KKT multipliers there. Define
--   $$
--   \mathcal L(x)=f(x)+\langle\lambda_*,h_1(x)\rangle+\langle\mu_*,g_1(x)\rangle+\langle v_*,h_2(x)\rangle+\langle u_*,g_2(x)\rangle,\qquad W=\nabla^2\mathcal L(x_*).
--   $$
--   Retain Assumption 11: $\langle Wz,z\rangle>0$ for every nonzero $z$ orthogonal to all equality gradients and all active inequality gradients, including those with zero multiplier. Retain Assumption 12: $\bar\lambda_{\min,i}<\lambda_{*,i}<\bar\lambda_{\max,i}$ and $0\le\mu_{*,j}<\bar\mu_{\max,j}$. Retain Assumption 13: $\mu_{*,i}>0$ whenever $g_{1,i}(x_*)=0$.
--
--   The correction also assumes the following regularity condition (R). Put $A_1=\{i:g_{1,i}(x_*)=0\}$, $A_2=\{i:g_{2,i}(x_*)=0\}$ and $A_2^+=\{i\in A_2:u_{*,i}>0\}$. For every $A_2^+\subseteq S\subseteq A_2$, let $V_S$ be the span of the gradients at $x_*$ of all components of $h_1,h_2$, of $g_{1,i}$ for $i\in A_1$, and of $g_{2,i}$ for $i\in S$. Require
--   $$
--   z\perp V_S\ \text{and}\ Wz\in V_S\quad\Longrightarrow\quad z=0.
--   $$
--   Under LICQ, this is nonsingularity of the KKT matrix for every candidate active set. It permits $g_{2,i}(x_*)=u_{*,i}=0$ and is not claimed to be necessary.
--
--   If there is a real sequence $\eta_k\to0$ such that, for every outer iteration $k\ge1$,
--   $$
--   \varepsilon_k\le\eta_k\max\{\|h_1(x_k)\|_\infty,\|\sigma_k\|_\infty\},\qquad [\sigma_k]_i=\max\{[g_1(x_k)]_i,-[\bar\mu_k]_i/\rho_k\},
--   $$
--   then
--   $$
--   \sup_{k\in\mathbb N}\rho_k<+\infty.
--   $$
--   This companion result gives sufficient conditions for bounded penalties in the general constrained problem. The printed Theorem 5.5 is false; the added premises and two counterexamples are documented in DISPROOF.md. No lower-level strict complementarity is assumed.
--
--   **Formalization Note** The conclusion is `BddAbove (Set.range ρ)`. The true gradient and Hessian are used under their differentiability hypotheses. Every finite dimension and every empty constraint family is allowed, subject to the stated assumptions. The published penalty definitions are used directly; the goal reference belongs to the separate feasibility namespace. The two new restrictions are exactly positive $\tau$ and (R).
--
--   Differences from the source:
--   - correction: Algorithm 3.1 permits τ = 0, and Theorem 5.5 adds no restriction. → Require 0 < τ, hence 0 < τ < 1 together with IsParams.; reason: The exact equality-constrained counterexample B in DISPROOF.md has unbounded penalties at τ = 0 even when (R) holds.
--   - correction: Assumptions 7–13 allow singular KKT systems after omitting weakly active lower-level constraints. → Add (R): every candidate active set between the strongly active and active lower-level constraints has nonsingular KKT matrix, in the explicit orthogonality-and-span form below.; reason: Counterexample A satisfies all printed assumptions for every admissible parameter triple. The reduction to (5.12) fails on weakly active lower-level constraints; (R) supplies the uniform inverse bounds for the finitely many candidate systems. It excludes singular candidate systems, without imposing lower-level strict complementarity.
--   - reading: The objective and constraints have continuous first derivatives on a sufficiently large open domain. → Use the published global C¹ convention on ℝⁿ.; reason: This is the standing interpretation of the published Problem.IsC1 interface; no base definition is modified.
--   - reading: Assumptions 11–13 name λ∗, μ∗, v∗, u∗ without explicitly introducing them. → Pin them as KKT multipliers of (2.1) at x∗ using IsKKTMult.; reason: The proof, p. 14, identifies them as the multipliers associated to (2.1); LICQ ensures uniqueness.
--   - encoding: The tolerance bound says for all k ∈ ℕ; Algorithm 3.1 starts its outer iterations at k = 1. → Impose the tolerance bound for every k ≥ 1 and preserve σ₀ as the initialization value.; reason: Index zero is the arbitrary initial point, not an outer subproblem; its unused penalty value does not affect boundedness.
--   - encoding: An arbitrary vector norm is allowed, with the sup norm explicitly required in Step 4. → Use EuclideanSpace ℝ (Fin n), the Euclidean norm in (3.1), and function-space sup norms for h₁, h₂ and σ.; reason: Finite-dimensional norm equivalence preserves vanishing tolerances and all claimed boundedness; Step 4 and the relative tolerance use precisely the specified sup norms.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, pp. 13–15, Assumptions 7–13, Theorem 5.5 (p. 14), proof and (5.12); corrected as documented in DISPROOF.md.

import Mathlib
import Definitions.Def_AugLagLLC_Penalty_Setting
import Definitions.Def_AugLagLLC_Penalty_SecondOrder

open Filter
open scoped Topology

namespace AugLagLLC.Feas.Supplement

/-- Theorem 5.5 (corrected), HAL hal-01295437v1, p. 14 (PDF 15).
Retains Assumptions 7–13 and adds `0 < τ` and candidate-active-set regularity (R).
The lower-level multipliers may vanish on active inequalities. In (R), the span is
of all equality gradients, active upper-level gradients and the selected lower-level
gradients. Under LICQ, (R) says each candidate KKT matrix at parameter zero is nonsingular.
The paper's unrestricted claim is false; see this supplement's DISPROOF.md. -/
theorem theorem_5_5
    {n m1 p1 m2 p2 : ℕ} (P : AugLagLLC.Penalty.Problem n m1 p1 m2 p2)
    (hP : P.IsC1)
    {τ γ ρ1 : ℝ} {lamMin lamMax : Fin m1 → ℝ} {muMax : Fin p1 → ℝ} {ε : ℕ → ℝ}
    (hpar : AugLagLLC.Penalty.Problem.IsParams τ γ ρ1 lamMin lamMax muMax ε)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {ρ : ℕ → ℝ}
    {lamBar : ℕ → Fin m1 → ℝ} {muBar : ℕ → Fin p1 → ℝ}
    {v : ℕ → Fin m2 → ℝ} {u : ℕ → Fin p2 → ℝ}
    -- The safeguard Definition of §5.2 and Assumption 7.
    (hrun : P.IsProjRun τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u)
    {xs : EuclideanSpace ℝ (Fin n)} (hlim : Tendsto x atTop (𝓝 xs))
    -- Assumptions 8–10.
    (hfeas : xs ∈ P.Omega1 ∩ P.Omega2)
    (hLICQ : AugLagLLC.Penalty.LICQAt (Sum.elim P.h1 P.h2) (Sum.elim P.g1 P.g2) xs)
    (hC2 : P.IsC2At xs)
    -- The multipliers named in Assumptions 11–13 are the KKT multipliers of (2.1).
    (lamS : Fin m1 → ℝ) (muS : Fin p1 → ℝ) (vS : Fin m2 → ℝ) (uS : Fin p2 → ℝ)
    (hKKT : P.IsKKTMult lamS muS vS uS xs)
    -- Assumptions 11–13, including all active gradients in the tangent subspace.
    (hSOSC : P.SOSC lamS muS vS uS xs)
    (hbox : ∀ i, lamMin i < lamS i ∧ lamS i < lamMax i)
    (hmubox : ∀ j, 0 ≤ muS j ∧ muS j < muMax j)
    (hstrict : ∀ i, P.g1 i xs = 0 → 0 < muS i)
    -- Corrections: positive contraction factor, and regularity for every candidate set.
    (hτ : 0 < τ)
    (hR : ∀ S : Set (Fin p2),
      {i | P.g2 i xs = 0 ∧ 0 < uS i} ⊆ S → S ⊆ {i | P.g2 i xs = 0} →
      ∀ z : EuclideanSpace ℝ (Fin n),
        (∀ i, inner ℝ (gradient (P.h1 i) xs) z = 0) →
        (∀ i, inner ℝ (gradient (P.h2 i) xs) z = 0) →
        (∀ i, P.g1 i xs = 0 → inner ℝ (gradient (P.g1 i) xs) z = 0) →
        (∀ i ∈ S, inner ℝ (gradient (P.g2 i) xs) z = 0) →
        AugLagLLC.Penalty.hess (P.lagr lamS muS vS uS) xs z ∈
          Submodule.span ℝ
            (Set.range (fun i : Fin m1 => gradient (P.h1 i) xs) ∪
             Set.range (fun i : Fin m2 => gradient (P.h2 i) xs) ∪
             Set.range (fun i : {i : Fin p1 // P.g1 i xs = 0} => gradient (P.g1 i) xs) ∪
             Set.range (fun i : S => gradient (P.g2 i) xs)) →
        z = 0)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hεη : ∀ k, 1 ≤ k → ε k ≤ η k * max ‖P.h1vec (x k)‖ ‖P.sigma x ρ muBar k‖) :
    BddAbove (Set.range ρ) := by sorry

end AugLagLLC.Feas.Supplement
