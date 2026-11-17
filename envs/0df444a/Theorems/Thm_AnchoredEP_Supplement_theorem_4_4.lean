-- Prove2me | Theorems.Thm_AnchoredEP_Supplement_theorem_4_4
-- name    : AnchoredEP.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:13:31.071722+00:00
-- url     : https://prove2.me/theorems/1956517f-2e79-46db-94ee-47f372e069c2
-- title:
--   Theorem 4.4 — AEP Newton: $\mathrm{res}^{\tan}(\hat z)\le\varepsilon$ within $\lceil(16L_2\|z_0-z^\ast\|^2/\varepsilon)^{2/5}\rceil$ outer iterations
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R^d$ be monotone with $L_2$-Lipschitz Jacobian, $\|DF(z)-DF(z')\|_{\mathrm{op}}\le L_2\|z-z'\|$, where $L_2>0$ (Assumption 4.1), let $H:\mathbb R^d\rightrightarrows\mathbb R^d$ be maximal monotone, and let $z^\ast$ be any solution of $0\in F(z)+H(z)$. Let $\varepsilon>0$, $z_0\in\mathbb R^d$ and $v_0\in H(z_0)$, and set
--   $$
--   T:=\Big\lceil\Big(\frac{16L_2\|z_0-z^\ast\|^2}{\varepsilon}\Big)^{2/5}\Big\rceil .
--   $$
--   Then:
--
--   1. the affine-model subproblems (17) of Algorithm 1 have exact solutions, so the Anchored Extra-Proximal Newton method is well defined;
--   2. for every exact subproblem solver, Algorithm 1 returns, after at most $T$ outer iterations (accepted AEP Newton updates), a point $\hat z$ together with $\hat v\in H(\hat z)$ such that $\|F(\hat z)+\hat v\|\le\varepsilon$, hence $\mathrm{res}^{\tan}(\hat z)\le\varepsilon$;
--   3. at every outer iteration the run reaches whose stop test fails, the bisection line search (Subroutine 1) terminates.
--
--   Together with the line-search bound of Theorem 4.6, this gives $\tilde O\big((L_2\|z_0-z^\ast\|^2/\varepsilon)^{2/5}\big)$ second-order oracle calls, matching the paper's lower bound for $p=2$ up to the logarithmic factor.
--
--   **Formalization Note** The run is modelled as the state after $k$ executions of the outer loop body; a return during iteration $k$, after $k$ accepted updates, makes the state after $k+1$ executions a returned one, so "at most $T$ outer iterations" is the statement that the state after $T+1$ executions has returned.
--
--   Differences from the source:
--   - encoding: Assumption 4.1: ‖DF(z) − DF(z′)‖_op ≤ L₂‖z − z′‖ for all z, z′ → Assumption51 2 L F = ContDiff ℝ 1 F ∧ ‖iteratedFDeriv ℝ 1 F z − iteratedFDeriv ℝ 1 F z′‖ ≤ L‖z − z′‖; reason: the Jacobian DF presupposed by the source exists and is continuous when it is Lipschitz, and ‖iteratedFDeriv ℝ 1 F z − iteratedFDeriv ℝ 1 F z′‖ = ‖DF(z) − DF(z′)‖_op; the same operators qualify
--   - encoding: initial point z₀ ∈ dom H and a choice v₀ ∈ H(z₀) (Algorithm 1 lines 1–2) → hypothesis v0 ∈ H z0; reason: v₀ ∈ H(z₀) is exactly the algorithm's initialization and implies z₀ ∈ dom H
--   - encoding: Algorithm 1 solves each subproblem (17) exactly; p.7 shows the solution exists and is unique → (∃ sol, IsNewtonSolver F H sol) ∧ ∀ sol, IsNewtonSolver F H sol → …; reason: the well-posedness that the algorithm presupposes is stated, and the claims hold for every solver map; since the solution is unique, every admissible solver gives the source's iterates
--   - encoding: returns after at most T outer iterations, an outer iteration being one accepted AEP Newton update (p.10) → newtonRun F L ε sol z0 v0 (T + 1) = .returned ẑ v̂ with T = ⌈(16 L ‖z0 − zstar‖² / ε)^(2/5)⌉₊; reason: the state after k loop executions is running exactly when k accepted updates were made; a return during iteration k ≤ T, after k ≤ T accepted updates, gives a returned state after k + 1 ≤ T + 1 executions, and returned states persist
--   - encoding: Subroutine 1 terminates at every outer iteration (presupposed by "Algorithm 1 returns"; p.9) → ∀ k s, newtonRun … k = .running s → ε < ‖F s.z + s.v‖ → ∃ n, NewtonLineSearchReturnsWithin F L ε sol z0 s n; reason: a non-terminating line search would make the run use the placeholder step of newtonStepSize; asserting termination rules out that junk run and is part of the source's claim that the algorithm returns
--   - encoding: res^tan(z) = inf over v ∈ H(z) of ‖F(z) + v‖ (+∞ on an empty set) → tangentResidual = real sInf of the image (0 on an empty set); reason: the same value whenever H(ẑ) is nonempty, which the stated membership v̂ ∈ H(ẑ) guarantees
--   - generalization: res^tan(ẑ) ≤ ε → additionally v̂ ∈ H(ẑ) and ‖F(ẑ) + v̂‖ ≤ ε for the returned certificate v̂; reason: the certificate implies the source's conclusion res^tan(ẑ) ≤ ε, which is also stated
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Theorem 4.4, p.10

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_AnchoredEP_IsSolution
import Definitions.Def_AnchoredEP_tangentResidual
import Definitions.Def_AnchoredEP_Assumption51
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_RunState
import Definitions.Def_AnchoredEP_Supplement_IsNewtonSolver
import Definitions.Def_AnchoredEP_Supplement_NewtonLineSearchReturnsWithin
import Definitions.Def_AnchoredEP_Supplement_newtonRun

open ThreeOpSplitting.Convergence

namespace AnchoredEP.Supplement

/-- **Theorem 4.4 (outer iteration complexity of AEP Newton).** Jiang–Yoon, *Anchored Extra-Proximal
Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems*, arXiv:2609.30212,
Theorem 4.4, p.10: "Algorithm 1 returns a point `ẑ` satisfying `res^tan(ẑ) ≤ ε` after at most
`T := ⌈(16L₂‖z₀ − z∗‖²/ε)^{2/5}⌉` outer iterations." Here (p.10) "an outer iteration refers to one
accepted AEP Newton update".

For every dimension `d`, every monotone `F : ℝ^d → ℝ^d` satisfying Assumption 4.1 with `L₂ > 0`,
every maximal monotone `H`, every `ε > 0`, every `z₀` and `v₀ ∈ H(z₀)`, and every solution `z∗` of
Problem (1), with `T := ⌈(16L₂‖z₀ − z∗‖²/ε)^{2/5}⌉`:
1. (well-posedness) an exact solver of the subproblems (17) exists, so Algorithm 1 is defined;
and for every such solver,
2. the run has returned after at most `T` accepted updates, i.e. `newtonRun … (T + 1)` is
   `.returned ẑ v̂`, with `v̂ ∈ H(ẑ)`, `‖F(ẑ) + v̂‖ ≤ ε` and `res^tan(ẑ) ≤ ε`;
3. at every outer iteration the run reaches whose stop test fails, Subroutine 1 returns (after
   finitely many trial evaluations).

**Formalization Note.** Assumption 4.1 (`‖DF(z) − DF(z′)‖_op ≤ L₂‖z − z′‖`) is the published
`Assumption51 2 L F` (`ContDiff ℝ 1 F` and the bound on `iteratedFDeriv ℝ 1 F`, whose norm
equals that of `fderiv ℝ F`). `newtonRun … k = .running s` means `k` accepted updates were made;
a return by the stop test or by the upper trial during iteration `k` makes `newtonRun … (k + 1)`
`.returned` after `k` accepted updates, so `newtonRun … (T + 1) = .returned …` is exactly "at most
`T` outer iterations". Clause 3 rules out runs that move on with the placeholder step of
`newtonStepSize`. `(·)^{2/5}` is `Real.rpow` and `⌈·⌉` is `Nat.ceil`. The certificate
`v̂ ∈ H(ẑ) ∧ ‖F(ẑ) + v̂‖ ≤ ε` is stated besides `res^tan(ẑ) ≤ ε` because the real `sInf` in
`tangentResidual` is `0` on an empty set. -/
theorem theorem_4_4 (d : ℕ) (L ε : ℝ)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
    (z0 v0 zstar : EuclideanSpace ℝ (Fin d))
    (hF : IsMonotoneOp (fun x => ({F x} : Set (EuclideanSpace ℝ (Fin d)))))
    (hH : IsMaximalMonotone H) (hsol : IsSolution F H zstar)
    (hA : Assumption51 2 L F) (hL : 0 < L) (hε : 0 < ε) (hv0 : v0 ∈ H z0) :
    (∃ sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), IsNewtonSolver F H sol) ∧
    ∀ sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), IsNewtonSolver F H sol →
      (∃ zhat vhat : EuclideanSpace ℝ (Fin d),
        newtonRun F L ε sol z0 v0
            (⌈(16 * L * ‖z0 - zstar‖ ^ 2 / ε) ^ ((2 : ℝ) / 5)⌉₊ + 1) = .returned zhat vhat ∧
          vhat ∈ H zhat ∧ ‖F zhat + vhat‖ ≤ ε ∧ tangentResidual F H zhat ≤ ε) ∧
      (∀ (k : ℕ) (s : IterState d), newtonRun F L ε sol z0 v0 k = .running s →
        ε < ‖F s.z + s.v‖ → ∃ n : ℕ, NewtonLineSearchReturnsWithin F L ε sol z0 s n) := by sorry

end AnchoredEP.Supplement
