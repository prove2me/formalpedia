-- Prove2me | Theorems.Thm_BregmanPPA_EqMult_theorem6_limit_points
-- name    : BregmanPPA.EqMult.theorem6_limit_points
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:26.325983+00:00
-- url     : https://prove2.me/theorems/d741ff3f-a7f8-4b7d-b1fb-e150d2ca7dc4
-- title:
--   Proof of Theorem 6 — when $p^k \to p^*$, $Ax^k \to b$ and every limit point of $\{x^k\}$ solves (7)
-- statement:
--   Assume the setting of Theorem 6: problem (7) with $X$ closed convex, $f : \mathbb R^n \to (-\infty,+\infty]$ convex and lower semicontinuous, $\inf_X f < \infty$, the dual functional $d$ not identically $-\infty$; $h$ a Bregman function with zone $\mathbb R^m$ and $\operatorname{im}\nabla h = \mathbb R^m$; scalars $c_k > 0$ with $\inf_k c_k > 0$; and $\{(x^k,p^k)\}$ conforming to recursion (9). Suppose that $p^k \to p^*$, where $p^*$ is an optimal multiplier (a maximizer of $d$), and let $x^\infty$ be a limit point of $\{x^k\}$, i.e. the limit of some subsequence $\{x^{k(j)}\}$. Then
--
--   1. $Ax^k \to b$;
--   2. $Ax^\infty = b$;
--   3. $-A^{\mathsf T}p^* \in \partial f_X(x^\infty)$, where $f_X = f + \delta_X$;
--   4. $x^\infty$ solves (7): $x^\infty \in X$, $Ax^\infty = b$, and $f(x^\infty) \le f(y)$ for every $y \in X$ with $Ay = b$.
--
--   This is the primal half of Theorem 6: once the multipliers converge to a Lagrange multiplier, the primal iterates are asymptotically feasible and all their limit points are optimal, even though $\{x^k\}$ itself need not converge.
--
--   **Formalization Note** A limit point is a subsequential limit: a strictly increasing $\varphi : \mathbb N \to \mathbb N$ with $x^{\varphi(j)} \to x^\infty$. $A^{\mathsf T}$ is the adjoint of the linear map $A$. The subdifferential is that of the `EReal` function $f + \delta_X$. The hypotheses are the standing assumptions of Theorem 6 together with the convergent case $p^k \to p^*$ considered in its proof.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 214, proof of Theorem 6 (from "Now consider the convergent case" to "So, x^∞ solves (7).")

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_fenchelConjugate
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_EqMult_EqConstrainedProgram

open InertialFB.IFB ConvexOptimization Filter Topology

namespace BregmanPPA.EqMult
theorem theorem6_limit_points {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hP : IsEqProgram X f) (hd : ∃ p, dualEq A b X f p ≠ ⊥)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h))
    (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (hcinf : ∃ ε > 0, ∀ k, ε ≤ c k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p)
    (pstar : EuclideanSpace ℝ (Fin m)) (hpstar : IsOptimalMultiplier A b X f pstar)
    (hp : Tendsto p atTop (𝓝 pstar))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (x' : EuclideanSpace ℝ (Fin n))
    (hx' : Tendsto (x ∘ φ) atTop (𝓝 x')) :
    Tendsto (fun k => A (x k)) atTop (𝓝 b) ∧ A x' = b ∧
    -(ContinuousLinearMap.adjoint A pstar) ∈ BregmanPPA.Convergence.subdiffOp (fX X f) x' ∧
    IsSolution7 A b X f x' := by sorry
end BregmanPPA.EqMult
