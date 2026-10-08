-- Prove2me | Theorems.Thm_CurveSymmetry_family_critical_mixed_iff
-- name    : CurveSymmetry.family_critical_mixed_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:25.284041+00:00
-- url     : https://prove2.me/theorems/79dd67a9-8522-4129-86eb-44f4faa41da4
-- title:
--   Singular points of $V_\alpha$ in the mixed chart $X=1/u$: homogeneous and affine Jacobian criteria agree
-- statement:
--   Let $m\ge0$ be an integer and let $\alpha\in\mathbb C$ be arbitrary. For $x=(x_0,x_1)$ and $y=(y_0,y_1)$ in $\mathbb C^2$ let
--
--   $$
--   F_\alpha(x,y)=\alpha\,x_0^m x_1\,y_1^{m+1}+x_0^{m+1}y_0\,y_1^m+\bar\alpha\,x_1^{m+1}y_0^m\,y_1+x_0\,x_1^m\,y_0^{m+1},
--   $$
--
--   the bihomogenization of $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$, and let $Q(u,Y)=\alpha u+Y+\bar\alpha\,u^{m+1}Y^m+u^mY^{m+1}\in\mathbb C[u,Y]$. It satisfies $Q(u,Y)=F_\alpha\bigl((1,u),(Y,1)\bigr)$, so $Q$ is the equation of $V_\alpha=\{F_\alpha=0\}\subset\mathbb P^1\times\mathbb P^1$ in the mixed chart of the points $([1:u],[Y:1])$, where $X=1/u$.
--
--   For all $u,Y\in\mathbb C$, the point $\bigl((1,u),(Y,1)\bigr)$ of $\mathbb C^2\times\mathbb C^2$ is a critical zero of $F_\alpha$, meaning that $F_\alpha$ vanishes there and is differentiable there with zero differential, if and only if
--
--   $$
--   Q(u,Y)=\frac{\partial Q}{\partial u}(u,Y)=\frac{\partial Q}{\partial Y}(u,Y)=0.
--   $$
--
--   In the proof of Lemma 4 the equation of $V_\alpha$ near the boundary point $(\infty,0)$ is written as $u^{m+1}P_\alpha(1/u,Y)=Q(u,Y)$. This lemma identifies the homogeneous singularity condition at the points $([1:u],[Y:1])$ with the Jacobian criterion for that chart equation; the formalization uses it to show that the mixed boundary points of $V_\alpha$ are nonsingular.
--
--   **Formalization Note**: the partial derivatives of $Q$ are Mathlib's formal derivatives `MvPolynomial.pderiv`, and the condition on $F_\alpha$ uses `HasFDerivAt` on `(Fin 2 → ℂ) × (Fin 2 → ℂ)`.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 4, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/HomogeneousCharts.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

open CurveSymmetry
set_option autoImplicit false
open Filter
open scoped Topology

theorem CurveSymmetry.family_critical_mixed_iff (m : ℕ) (α x y : ℂ) :
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
      (![1, x], ![y, 1]) ↔ JacobianSingular (familyMixedPolynomial m α (star α)) x y := by sorry
