-- Prove2me | Theorems.Thm_AnchoredEP_eq_87
-- name    : AnchoredEP.eq_87
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:33.140366+00:00
-- url     : https://prove2.me/theorems/6c50a0a3-1df0-45e0-8f1e-121ec87afe9e
-- title:
--   Eq. (87) — the regularized Taylor-model subproblem has a unique solution
-- statement:
--   Let $p\ge2$, let $F$ be monotone and satisfy Assumption 5.1 with $L_p>0$, let $H$ be maximal monotone, and assume Problem (1) has a solution. Then for every step $a>0$, every center $y\in\mathbb R^d$ and every point $w\in\mathbb R^d$ there is exactly one $z\in\mathbb R^d$ with
--   $$
--   0\in a\,\mathbb T^{(p-1)}_{L_p}(z;y)+aH(z)+z-w .
--   $$
--   Consequently an exact subproblem solver exists, and Algorithm 3 is well defined: each trial point $z_{k+1}(a)$ of the line search, the solution of (87) for $y=z_{k+\frac12}(a)$ and $w=\frac{a}{A_k+a}z_0+\frac{A_k}{A_k+a}z_k$, exists and is unique.
--
--   Differences from the source:
--   - encoding: the (p−1)th derivative of F exists and is L_p-Lipschitz (Assumption 5.1) → Assumption51 p L F = ContDiff ℝ (p−1) F ∧ ‖iteratedFDeriv (p−1) F z − iteratedFDeriv (p−1) F z′‖ ≤ L‖z − z′‖; reason: the existence of D^{p−1}F is presupposed by the source; a Lipschitz (p−1)th derivative is continuous, so the same operators qualify
--   - generalization: y = z_{k+½}(a) and w = a/(A_k+a) z₀ + A_k/(A_k+a) z_k → all y, w ∈ ℝ^d; reason: the algorithm's center and anchored point are particular points of ℝ^d
--   - encoding: z_{k+1}(a) is the unique solution of (87) → ∃! z, … and also ∃ sol, IsSubSolver F H p L sol; reason: the solver map is the choice of the unique solution for each (a, y, w)
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix G.2, Eq. (87), p.37

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_AnchoredEP_IsSolution
import Definitions.Def_AnchoredEP_Assumption51
import Definitions.Def_AnchoredEP_regTaylor
import Definitions.Def_AnchoredEP_IsSubSolver

open ThreeOpSplitting.Convergence

namespace AnchoredEP

/-- **Eq. (87): the trial subproblem has a unique solution.** Jiang–Yoon, arXiv:2609.30212,
Appendix G.2, Eq. (87), p.37: "let `z_{k+1}(a)` be the unique solution of
`0 ∈ a P_{k,a}(z_{k+1}(a)) + a H(z_{k+1}(a)) + z_{k+1}(a) − (a/(A_k + a) z₀ + A_k/(A_k + a) z_k)`",
with `P_{k,a} = 𝕋_λ^{(p−1)}(·; z_{k+½}(a))`, `λ = L_p` (also p.11: the regularization makes `P_k`
maximal monotone "so that the resulting subproblem is guaranteed to have a unique solution").

Under the standing assumptions (`F` monotone, `H` maximal monotone, Problem (1) solvable) and
Assumption 5.1 with `L_p > 0`: for every step `a > 0`, every Taylor center `y` and every point
`w`, there is exactly one `z` with `0 ∈ a 𝕋_{L_p}^{(p−1)}(z; y) + a H(z) + z − w`. Consequently a
subproblem solver in the sense of `IsSubSolver` exists, i.e. Algorithm 3 is well defined.

**Formalization Note.** `y` and `w` range over all of `ℝ^d` (in the algorithm they are
`z_{k+½}(a)` and `a/(A_k + a) z₀ + A_k/(A_k + a) z_k`). -/
theorem eq_87 {d : ℕ} (p : ℕ) (hp : 2 ≤ p) (L : ℝ)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsMonotoneOp (fun x => ({F x} : Set (EuclideanSpace ℝ (Fin d)))))
    (hH : IsMaximalMonotone H) (hsolv : ∃ zstar, IsSolution F H zstar)
    (hA : Assumption51 p L F) (hL : 0 < L) :
    (∀ a : ℝ, 0 < a → ∀ y w : EuclideanSpace ℝ (Fin d),
      ∃! z : EuclideanSpace ℝ (Fin d), ∃ h ∈ H z, a • regTaylor F p L y z + a • h + z - w = 0) ∧
    ∃ sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      IsSubSolver F H p L sol := by sorry

end AnchoredEP
