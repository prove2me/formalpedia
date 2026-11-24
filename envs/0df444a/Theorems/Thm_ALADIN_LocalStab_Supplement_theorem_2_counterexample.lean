-- Prove2me | Theorems.Thm_ALADIN_LocalStab_Supplement_theorem_2_counterexample
-- name    : ALADIN.LocalStab.Supplement.theorem_2_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:11:32.576677+00:00
-- url     : https://prove2.me/theorems/75de16b9-2e1f-4593-901e-6c6840f8e64a
-- title:
--   Theorem 2 (corrected: counterexample) — Algorithm 3 can have no permitted output
-- statement:
--   Use the disk-exterior problem $\min u^2$ subject to $v=0$, $u^2+v^2\ge1$. Initialize $x=(0,1)$ and $\lambda=0$; take any exact-penalty weights $L,K\ge4$ (all of them exact), any fixed $\gamma>0$, and $0<\epsilon<1$. For every $\rho>0$ and $\mu\ge\rho$, there are globally solved NLPs and QPs whose first globalization step is
--   $$ (\alpha_1,\alpha_2,\alpha_3)=(0,0,\rho/\mu),\qquad (x^+,\lambda^+)=((0,1),\rho). $$
--   At that next state both stopping tests are retained and the coupling test fails. Both primal candidates equal $x$, so neither descent branch is accepted. The dual direction is positive, whereas $V_\rho(x,\lambda)$ has its unique maximum at $\lambda=\rho$; on the permitted interval $(0,1]$ its supremum along that direction is not attained. Algorithm 3 has no output.
--
--   The problem is feasible, has attained minimum $1$, bounded objective Hessians, regular original minima and regular projection minimizers at every center of this prefix. All local NLP solutions used satisfy LICQ. This counterexample target contradicts the source's claimed well-definedness and unconditional finite termination; it does not assert the existence of an infinite valid execution after a nonexistent maximizer. Its draft proof is open; DISPROOF.md supplies the mathematical derivation.
--
--   Differences from the source:
--   - correction: The source asserts that the algorithm is well-defined and terminates finitely under the stated global assumptions. → A legal one-step prefix from fixed initialization reaches an unstopped state with no permitted globalization output, for arbitrarily large rho and mu.; reason: The dual maximizer is at the excluded endpoint alpha=0; feasibility of the NLP and QP does not ensure existence of the line search.
--   - encoding: Finite real block vectors and the source optimization problems. → The published Fin-indexed carrier, explicit one-norm and quadratic forms, and extended-real value infima.; reason: Preserves the base definitions and avoids total real infimum defaults; counterexample data are explicit.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), DOI 10.1137/140975991, p. 1116, Theorem 2; explicit counterexample, see local DISPROOF.md

import Mathlib
import Definitions.Def_ALADIN_LocalStab_Supplement_Countermodels

namespace ALADIN.LocalStab.Supplement

/-- Theorem 2, p.1116: for all exact-penalty weights L, K ≥ 4, every ρ > 0, μ ≥ ρ and γ > 0,
a legal prefix from fixed initialization (north,0) reaches an
unstopped state where Algorithm 3 has no output. This is failure of well-definedness,
not a claimed infinite execution satisfying an impossible line-search relation. -/
theorem theorem_2_counterexample :
    SmoothRegularProblem diskProblem ∧ BoundedObjectiveHessians diskProblem ∧
    (∀ L K : ℝ, 4 ≤ L → 4 ≤ K → ExactPenalty diskProblem L K) ∧
    GlobalMin diskProblem east ∧
    (∀ z ∈ diskProblem.feasibleSet, 1 ≤ diskProblem.objective z) ∧
    GlobalMin (projectionProblem diskProblem diskScaling north) east ∧
    (∀ z, GlobalMin (projectionProblem diskProblem diskScaling north) z →
      (projectionProblem diskProblem diskScaling north).IsRegularKKTPoint
        z (fun _ => 1) (fun _ _ => 1/2)) ∧
    ∀ (L K ρ μ γ ε : ℝ), 4 ≤ L → 4 ≤ K → 0 < ρ → ρ ≤ μ → 0 < γ → 0 < ε → ε < 1 →
      let D₀ := diskStep ρ μ 0
      let D₁ := diskStep ρ μ ρ
      Prepared diskProblem north 0 D₀ ∧
      Prepared diskProblem north (fun _ => ρ) D₁ ∧
      (∀ i z, z ∈ decoupledFeasibleSet diskProblem i →
        decoupledObjective diskProblem ρ diskScaling north 0 i (D₀.y i) ≤
          decoupledObjective diskProblem ρ diskScaling north 0 i z) ∧
      (∀ i z, z ∈ decoupledFeasibleSet diskProblem i →
        decoupledObjective diskProblem ρ diskScaling north (fun _ => ρ) i (D₁.y i) ≤
          decoupledObjective diskProblem ρ diskScaling north (fun _ => ρ) i z) ∧
      ¬ Stops diskProblem north ε D₀ ∧ ¬ Stops diskProblem north ε D₁ ∧
      Globalization diskProblem L K γ north 0 D₀ 0 0 (ρ/μ) ∧
      nextX north D₀ 0 0 = north ∧ nextLam 0 D₀ (ρ/μ) = (fun _ => ρ) ∧
      ¬ ∃ a₁ a₂ a₃ : ℝ,
        Globalization diskProblem L K γ north (fun _ => ρ) D₁ a₁ a₂ a₃ := by sorry

end ALADIN.LocalStab.Supplement
