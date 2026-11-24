-- Prove2me | Theorems.Thm_ALADIN_LocalStab_Supplement_theorem_4_counterexample
-- name    : ALADIN.LocalStab.Supplement.theorem_4_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:12:19.048615+00:00
-- url     : https://prove2.me/theorems/c292fc34-1d97-4847-94c7-1b6e77531c25
-- title:
--   Theorem 4 (corrected: counterexample) — exact data can require a fractional dual step
-- statement:
--   Consider $f(q)=q^2/2+q^3/3+q^4/4$ with equality $q=0$ and one always inactive inequality $-1\le0$. The solution $(x^*,\lambda^*)=(0,0)$ is regular, $f$ is globally strictly convex, and every positive penalty weight is exact. Fix any $\rho>0$, any positive exact-penalty weights and $\gamma>0$. Arbitrarily close to this solution, choose $x=0$, $y=t>0$, $\lambda=-((1+\rho)t+t^2+t^3)$, exact Hessian $H=1+2t+3t^2$, and $\mu=t^{-2}$. The exact QP gives $z=(H+\rho)t/(H+\mu)$ and $\lambda_{QP}=\lambda+\mu z$. For all sufficiently small $t$ the dual step overshoots: $\lambda<0<\lambda_{QP}$. Both primal trials fail the descent test, and the unique ordered globalization output is
--   $$\alpha_1=\alpha_2=0,\qquad \alpha_3=\frac{-\lambda}{\lambda_{QP}-\lambda}\in(0,1).$$
--   The statement quantifies every local radius and every lower bound on $\mu$, with the QP and NLP solved globally and derivative data exact at the current $y$. In particular $1/\mu=t^2$, so the failure persists even with the vanishing regularization discussed around p. 1118. This refutes Theorem 4's full-dual-step assertion in its exact-data subcase, hence the full printed theorem. Exact data also have zero approximation errors at these points, but no separate assertion is made about infinitely many bad steps on one consistent-approximation trajectory. The draft proof is open; DISPROOF.md retains the exact calculation.
--
--   Differences from the source:
--   - correction: The source asserts only (1,1,1) or (0,0,1) near a regular solution, including exact and consistent derivative data. → An exact-data family arbitrarily close to the solution has the unique output (0,0,a) with 0<a<1; this refutes the whole theorem through its exact subcase.; reason: The exact Newton direction can overshoot the unique dual maximizer, so the exact line search truncates it. Excluding branch (b) alone cannot prove alpha_3=1.
--   - encoding: Finite real block vectors and the source optimization problems. → The published Fin-indexed carrier, explicit one-norm and quadratic forms, and extended-real value infima.; reason: Preserves the base definitions and avoids total real infimum defaults; counterexample data are explicit.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), DOI 10.1137/140975991, p. 1119, Theorem 4; explicit counterexample, see local DISPROOF.md

import Mathlib
import Definitions.Def_ALADIN_LocalStab_Supplement_Countermodels

namespace ALADIN.LocalStab.Supplement

open Matrix

/-- Theorem 4, p.1119: exact derivatives can give an interior dual line-search maximizer
arbitrarily close to the regular solution, even with mu arbitrarily large and 1/mu=t^2.
The exact subcase already refutes the claimed exact-or-consistent universal conclusion. -/
theorem theorem_4_counterexample :
    SmoothRegularProblem quarticProblem ∧
    quarticProblem.IsLocalMinimizer 0 ∧ quarticProblem.IsRegularKKTPoint 0 0 0 ∧
    (∀ L K : ℝ, 0 < L → 0 < K → ExactPenalty quarticProblem L K) ∧
    ∀ ρ : ℝ, 0 < ρ →
      (∀ i (d : Fin 1 → ℝ), d ≠ 0 →
        0 < hessQuad (quarticProblem.lagBlock i 0) 0 d +
          ρ * (d ⬝ᵥ (scalarScaling i *ᵥ d))) ∧
      ∀ (L K γ δ M : ℝ), 0 < L → 0 < K → 0 < γ → 0 < δ → 0 < M →
        ∃ t : ℝ, 0 < t ∧ t < δ ∧
          let D := quarticStep ρ t
          let lam := quarticLam ρ t
          ‖lam‖ < δ ∧ ‖D.y‖ < δ ∧ M < D.μ ∧
          Prepared quarticProblem 0 lam D ∧
          (∀ i, D.C i = activeJac quarticProblem D.y i ∧
            D.H i = exactHessian quarticProblem D.y D.κ i) ∧
          (∀ i z, z ∈ decoupledFeasibleSet quarticProblem i →
            decoupledObjective quarticProblem ρ scalarScaling 0 lam i (D.y i) ≤
              decoupledObjective quarticProblem ρ scalarScaling 0 lam i z) ∧
          (∃ ε : ℝ, 0 < ε ∧ ¬ Stops quarticProblem 0 ε D) ∧
          0 < quarticQP ρ t ∧ 0 < quarticAlpha ρ t ∧ quarticAlpha ρ t < 1 ∧
          Globalization quarticProblem L K γ 0 lam D 0 0 (quarticAlpha ρ t) ∧
          (∀ a₁ a₂ a₃ : ℝ, Globalization quarticProblem L K γ 0 lam D a₁ a₂ a₃ →
            a₁ = 0 ∧ a₂ = 0 ∧ a₃ = quarticAlpha ρ t) := by sorry

end ALADIN.LocalStab.Supplement
