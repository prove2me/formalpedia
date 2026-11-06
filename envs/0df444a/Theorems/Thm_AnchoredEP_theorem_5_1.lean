-- Prove2me | Theorems.Thm_AnchoredEP_theorem_5_1
-- name    : AnchoredEP.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:48:37.840411+00:00
-- url     : https://prove2.me/theorems/8c94e1e7-4c57-45e2-b553-834004c57e58
-- title:
--   Theorem 5.1 — complexity of the AEP Tensor Method
-- statement:
--   For every order $p\ge2$ there is a constant $C>0$, depending only on $p$, with the following property. Let $F:\mathbb R^d\to\mathbb R^d$ be monotone and satisfy Assumption 5.1 with $L_p>0$, let $H$ be maximal monotone, let $\varepsilon>0$, $z_0\in\mathbb R^d$ and $v_0\in H(z_0)$, let $z^\ast$ be any solution of $0\in F(z)+H(z)$, and set
--   $$
--   Q=\frac{L_p\|z_0-z^\ast\|^p}{\varepsilon}.
--   $$
--   Then the regularized Taylor-model subproblems of Algorithm 3 have exact solutions, and with any exact subproblem solver the Anchored Extra-Proximal Tensor Method (Algorithm 3):
--
--   1. returns, after at most $C\big(1+Q^{2/(3p-1)}\big)$ outer iterations, a point $\hat z$ together with $\hat v\in H(\hat z)$ such that $\|F(\hat z)+\hat v\|\le\varepsilon$, so that $\mathrm{res}^{\tan}(\hat z)\le\varepsilon$;
--   2. uses, at every outer iteration that performs a line search, at most $C\big(1+\log(1+Q)\big)$ trial evaluations, the initial upper trial included.
--
--   Each trial costs one $p$th-order oracle call and one subproblem solve, so the total oracle complexity is $\tilde O_p\big((L_p\|z_0-z^\ast\|^p/\varepsilon)^{2/(3p-1)}\big)$, which matches the paper's lower bound for $p$th-order methods up to the logarithmic factor.
--
--   Differences from the source:
--   - encoding: the (p−1)th derivative of F exists and is L_p-Lipschitz (Assumption 5.1) → Assumption51 p L F = ContDiff ℝ (p−1) F ∧ ‖iteratedFDeriv (p−1) F z − iteratedFDeriv (p−1) F z′‖ ≤ L‖z − z′‖; reason: the existence of D^{p−1}F is presupposed by the source; a Lipschitz (p−1)th derivative is continuous, so the same operators qualify
--   - encoding: outer iteration k of Algorithm 3 (exact subproblem solutions) → a state s with tensorRun F p L ε sol z0 v0 k = .running s, for every solver sol with IsSubSolver; reason: Algorithm 3 as a deterministic run with its subproblem oracle as a parameter; the solution of (87) is unique, so every admissible solver gives the source's run
--   - encoding: a constant C_p > 0 depending only on p → ∃ C > 0 quantified after p and before the dimension and all data; reason: the source's O_p / C_p convention
--   - encoding: returns after at most T outer iterations (the stop test at iteration T returns z_T) → tensorRun … N = .returned ẑ v̂ with N ≤ C(1 + Q^{2/(3p−1)}): N counts executions of the outer loop body, a return at iteration k giving N = k + 1; reason: the count differs from the source's by at most one, absorbed in the existential constant
--   - encoding: at most O_p(1 + log(1 + Q)) trial evaluations per iteration → at every reached state whose stop test fails, ∃ n ≤ C(1 + log(1 + Q)) with LineSearchReturnsWithin … n; reason: iterations that stop at the test perform no trial; the predicate counts the upper trial and the final accepted trial and asserts that the search returns
--   - encoding: Algorithm 3 solves each subproblem (87) exactly → (∃ sol, IsSubSolver F H p L sol) ∧ ∀ sol, IsSubSolver F H p L sol ⟹ …; reason: the well-posedness that 'Algorithm 3 returns' presupposes is stated, and the claims hold for every solver map (the solution of (87) is unique)
--   - encoding: res^tan(z) = inf over H(z) of ‖F(z)+v‖ (+∞ on an empty set) → tangentResidual = real sInf of the image (0 on an empty set); reason: the same value whenever H(z) is nonempty, which the stated membership guarantees
--   - generalization: res^tan(ẑ) ≤ ε → additionally v̂ ∈ H(ẑ) and ‖F(ẑ) + v̂‖ ≤ ε; reason: the returned certificate implies the source's conclusion
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Theorem 5.1, p.11

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_AnchoredEP_IsSolution
import Definitions.Def_AnchoredEP_tangentResidual
import Definitions.Def_AnchoredEP_Assumption51
import Definitions.Def_AnchoredEP_IsSubSolver
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_LineSearchReturnsWithin
import Definitions.Def_AnchoredEP_RunState
import Definitions.Def_AnchoredEP_tensorRun

open ThreeOpSplitting.Convergence

namespace AnchoredEP

/-- **Theorem 5.1 (complexity of the AEP Tensor Method).** Jiang–Yoon, *Anchored Extra-Proximal
Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems*, arXiv:2609.30212,
Theorem 5.1, p.11: "Under Assumption 5.1, Algorithm 3 returns a point `ẑ` satisfying
`res^tan(ẑ) ≤ ε` after at most `O_p(1 + (L_p‖z₀ − z∗‖^p/ε)^{2/(3p−1)})` outer iterations, with at most
`O_p(1 + log(1 + L_p‖z₀ − z∗‖^p/ε))` trial evaluations per iteration." The `O_p` convention (p.11):
"constants hidden by `O_p` may depend on the fixed order `p`, but not on `L_p`, `ε`, or the initial
distance."

For every order `p ≥ 2` there is a constant `C > 0` such that for every dimension `d`, every
monotone `F : ℝ^d → ℝ^d` satisfying Assumption 5.1 with `L_p > 0`, every maximal monotone `H`, every
`ε > 0`, every `z₀` and `v₀ ∈ H(z₀)`, and every solution `z∗` of Problem (1), with
`Q := L_p‖z₀ − z∗‖^p/ε`:
1. (well-posedness) an exact solver of the subproblems (87) exists, so Algorithm 3 is defined;
and for every such solver,
2. (outer iterations) after some `N ≤ C(1 + Q^{2/(3p−1)})` outer iterations the run has returned a
   point `ẑ` with a vector `v̂ ∈ H(ẑ)` such that `‖F(ẑ) + v̂‖ ≤ ε`, hence `res^tan(ẑ) ≤ ε`;
3. (trials per iteration) at every outer iteration the run reaches whose stop test fails, the
   line search returns within `C(1 + log(1 + Q))` trial evaluations (the upper trial included).

**Formalization Note.** `tensorRun … N = .returned ẑ v̂` means the run returned within the first
`N` executions of the outer loop body; a return by the stop test at iteration `k` is counted as
`k + 1`, a return by the upper trial during iteration `k` as `k + 1` (the source's count plus at
most one, absorbed in `C`). Trial evaluations are counted by `LineSearchReturnsWithin`, which also
asserts that the line search returns. The subproblem solver is a parameter quantified over all
maps satisfying `IsSubSolver`. `Q^{2/(3p−1)}` is a real power and `log` is `Real.log`. The
certificate `v̂ ∈ H(ẑ) ∧ ‖F(ẑ) + v̂‖ ≤ ε` is stated besides `res^tan(ẑ) ≤ ε` because the real `sInf`
in `tangentResidual` is `0` on an empty set. -/
theorem theorem_5_1 (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (L ε : ℝ)
      (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
      (z0 v0 zstar : EuclideanSpace ℝ (Fin d)),
      IsMonotoneOp (fun x => ({F x} : Set (EuclideanSpace ℝ (Fin d)))) →
      IsMaximalMonotone H → IsSolution F H zstar →
      Assumption51 p L F → 0 < L → 0 < ε → v0 ∈ H z0 →
      (∃ sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        IsSubSolver F H p L sol) ∧
      ∀ sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        IsSubSolver F H p L sol →
        (∃ N : ℕ, (N : ℝ) ≤ C * (1 + (L * ‖z0 - zstar‖ ^ p / ε) ^ ((2 : ℝ) / (3 * (p : ℝ) - 1))) ∧
          ∃ zhat vhat : EuclideanSpace ℝ (Fin d),
            tensorRun F p L ε sol z0 v0 N = .returned zhat vhat ∧
            vhat ∈ H zhat ∧ ‖F zhat + vhat‖ ≤ ε ∧ tangentResidual F H zhat ≤ ε) ∧
        (∀ (k : ℕ) (s : IterState d), tensorRun F p L ε sol z0 v0 k = .running s →
          ε < ‖F s.z + s.v‖ →
          ∃ n : ℕ, (n : ℝ) ≤ C * (1 + Real.log (1 + L * ‖z0 - zstar‖ ^ p / ε)) ∧
            LineSearchReturnsWithin F p L ε sol z0 s n) := by sorry

end AnchoredEP
