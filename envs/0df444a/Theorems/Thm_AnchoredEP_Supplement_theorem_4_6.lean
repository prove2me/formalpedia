-- Prove2me | Theorems.Thm_AnchoredEP_Supplement_theorem_4_6
-- name    : AnchoredEP.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:14:23.001208+00:00
-- url     : https://prove2.me/theorems/3ea531ca-55a3-4a2f-92a5-5a6df34c3708
-- title:
--   Theorem 4.6 — Subroutine 1 returns within $O(1+\log(1+L_2\|z_0-z^\ast\|^2/\varepsilon))$ trial evaluations
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $F:\mathbb R^d\to\mathbb R^d$ be monotone with $L_2$-Lipschitz Jacobian, $L_2>0$ (Assumption 4.1), let $H$ be maximal monotone, let $z^\ast$ be any solution of $0\in F(z)+H(z)$, and let $\varepsilon>0$, $z_0\in\mathbb R^d$, $v_0\in H(z_0)$. Then the subproblems (17) have exact solutions, and for every exact subproblem solver, at every outer iteration of Algorithm 1 before termination (the run has reached state $(z_k,v_k,A_k)$ and $\|F(z_k)+v_k\|>\varepsilon$), the bisection line search Subroutine 1 returns after at most
--   $$
--   C\Big(1+\log\Big(1+\frac{L_2\|z_0-z^\ast\|^2}{\varepsilon}\Big)\Big)
--   $$
--   trial evaluations, the initial trial at $a=\bar a_k$ included.
--
--   A trial evaluation costs one second-order oracle call and one solve of the affine-model subproblem, so this bounds the per-iteration oracle cost of the AEP Newton method.
--
--   Differences from the source:
--   - encoding: Assumption 4.1: ‖DF(z) − DF(z′)‖_op ≤ L₂‖z − z′‖ for all z, z′ → Assumption51 2 L F = ContDiff ℝ 1 F ∧ ‖iteratedFDeriv ℝ 1 F z − iteratedFDeriv ℝ 1 F z′‖ ≤ L‖z − z′‖; reason: the Jacobian DF presupposed by the source exists and is continuous when it is Lipschitz, and ‖iteratedFDeriv ℝ 1 F z − iteratedFDeriv ℝ 1 F z′‖ = ‖DF(z) − DF(z′)‖_op; the same operators qualify
--   - encoding: initial point z₀ ∈ dom H and a choice v₀ ∈ H(z₀) (Algorithm 1 lines 1–2) → hypothesis v0 ∈ H z0; reason: v₀ ∈ H(z₀) is exactly the algorithm's initialization and implies z₀ ∈ dom H
--   - encoding: Algorithm 1 solves each subproblem (17) exactly; p.7 shows the solution exists and is unique → (∃ sol, IsNewtonSolver F H sol) ∧ ∀ sol, IsNewtonSolver F H sol → …; reason: the well-posedness that the algorithm presupposes is stated, and the claims hold for every solver map; since the solution is unique, every admissible solver gives the source's iterates
--   - encoding: O(1 + log(1 + L₂‖z₀ − z∗‖²/ε)) with an absolute constant → ∃ C > 0 quantified before the dimension and all data, and n ≤ C(1 + Real.log (1 + L‖z0 − zstar‖²/ε)); reason: the order p = 2 is fixed, so the hidden constant is absolute
--   - encoding: at every outer iteration before termination, Subroutine 1 returns after at most n trial evaluations, including the initial trial at ā_k → ∀ k s, newtonRun … k = .running s → ε < ‖F s.z + s.v‖ → ∃ n ≤ C(…), NewtonLineSearchReturnsWithin F L ε sol z0 s n; reason: an iteration before termination is a reached running state whose stop test fails; the predicate counts the upper trial and the final accepted trial and asserts that the search returns
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Theorem 4.6, p.10

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_AnchoredEP_IsSolution
import Definitions.Def_AnchoredEP_Assumption51
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_RunState
import Definitions.Def_AnchoredEP_Supplement_IsNewtonSolver
import Definitions.Def_AnchoredEP_Supplement_NewtonLineSearchReturnsWithin
import Definitions.Def_AnchoredEP_Supplement_newtonRun

open ThreeOpSplitting.Convergence

namespace AnchoredEP.Supplement

/-- **Theorem 4.6 (line-search complexity of AEP Newton).** Jiang–Yoon, arXiv:2609.30212,
Theorem 4.6, p.10: "At every outer iteration before termination, Subroutine 1 returns after
`O(1 + log(1 + L₂‖z₀ − z∗‖²/ε))` trial evaluations, including the initial trial at `a = ā_k`."

There is an absolute constant `C > 0` such that for every dimension `d`, every monotone
`F : ℝ^d → ℝ^d` satisfying Assumption 4.1 with `L₂ > 0`, every maximal monotone `H`, every
`ε > 0`, every `z₀` and `v₀ ∈ H(z₀)`, and every solution `z∗` of Problem (1): an exact solver of
the subproblems (17) exists, and for every such solver, at every outer iteration of Algorithm 1
that the run reaches and whose stop test fails, Subroutine 1 returns within
`C(1 + log(1 + L₂‖z₀ − z∗‖²/ε))` trial evaluations, the initial trial at `ā_k` included.

**Formalization Note.** Assumption 4.1 is the published `Assumption51 2 L F`. The `O(·)` is
an existential constant chosen before the dimension and all data (the order `p = 2` is fixed).
Trial evaluations are counted by `NewtonLineSearchReturnsWithin`, which counts the upper trial
and the final accepted bisection trial and asserts that the search returns. "Before termination"
is a reached state `newtonRun … k = .running s` whose stop test `‖F(z_k) + v_k‖ ≤ ε` fails. `log`
is `Real.log`. -/
theorem theorem_4_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (L ε : ℝ)
      (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
      (z0 v0 zstar : EuclideanSpace ℝ (Fin d)),
      IsMonotoneOp (fun x => ({F x} : Set (EuclideanSpace ℝ (Fin d)))) →
      IsMaximalMonotone H → IsSolution F H zstar →
      Assumption51 2 L F → 0 < L → 0 < ε → v0 ∈ H z0 →
      (∃ sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), IsNewtonSolver F H sol) ∧
      ∀ sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), IsNewtonSolver F H sol →
        ∀ (k : ℕ) (s : IterState d), newtonRun F L ε sol z0 v0 k = .running s →
          ε < ‖F s.z + s.v‖ →
          ∃ n : ℕ, (n : ℝ) ≤ C * (1 + Real.log (1 + L * ‖z0 - zstar‖ ^ 2 / ε)) ∧
            NewtonLineSearchReturnsWithin F L ε sol z0 s n := by sorry

end AnchoredEP.Supplement
