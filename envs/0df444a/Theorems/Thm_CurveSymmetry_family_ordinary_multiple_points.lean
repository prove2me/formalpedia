-- Prove2me | Theorems.Thm_CurveSymmetry_family_ordinary_multiple_points
-- name    : CurveSymmetry.family_ordinary_multiple_points
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:42:05.488771+00:00
-- url     : https://prove2.me/theorems/bc3b5050-9f4c-4811-9e03-6c0906cc1e3e
-- title:
--   Chart equations of $V_\alpha$: ordinary $m$-fold points at $(0,0)$ and $(\infty,\infty)$, all other zeros simple
-- statement:
--   Let $m\ge 2$ be an integer and let $\alpha\in\mathbb{C}$ with $\alpha\ne\bar\alpha$ (no condition on $|\alpha|$). Consider the four complex polynomials in two variables
--
--   - $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$,
--   - $Q_\alpha(u,v)=u^m+v^m+uv(\bar\alpha u^m+\alpha v^m)$,
--   - $M_\alpha(u,Y)=\alpha u+Y+\bar\alpha u^{m+1}Y^m+u^mY^{m+1}$,
--   - $M'_\alpha(v,X)=\bar\alpha v+X+\alpha v^{m+1}X^m+v^mX^{m+1}$,
--
--   which are the equations of the curve $V_\alpha\subset\mathbb{P}^1\times\mathbb{P}^1$ in the four standard charts, with $u=1/X$ and $v=1/Y$. A polynomial $F(s,t)$ has multiplicity $n$ at $(s_0,t_0)\in\mathbb{C}^2$ if $F\in\mathfrak{m}^n\setminus\mathfrak{m}^{n+1}$, where $\mathfrak{m}=(s-s_0,\,t-t_0)$. It has an ordinary $n$-fold point at the origin if it has multiplicity $n$ at $(0,0)$ and its homogeneous component $F_n$ of degree $n$ is a product of $n$ pairwise non-proportional nonzero linear forms:
--
--   $$F_n(s,t)=c\prod_{i=1}^{n}(\lambda_i s+\mu_i t),\qquad c\ne0,\quad (\lambda_i,\mu_i)\ne(0,0),\quad \lambda_i\mu_j-\mu_i\lambda_j\ne0\ \ (i\ne j).$$
--
--   Then:
--
--   1. $P_\alpha$ has an ordinary $m$-fold point at $(0,0)$;
--   2. $Q_\alpha$ has an ordinary $m$-fold point at $(0,0)$;
--   3. every zero $(x,y)\ne(0,0)$ of $P_\alpha$ in $\mathbb{C}^2$ has multiplicity $1$;
--   4. every zero $(u,v)\ne(0,0)$ of $Q_\alpha$ in $\mathbb{C}^2$ has multiplicity $1$;
--   5. every zero $(u,y)\in\mathbb{C}^2$ of $M_\alpha$ has multiplicity $1$;
--   6. every zero $(v,x)\in\mathbb{C}^2$ of $M'_\alpha$ has multiplicity $1$.
--
--   Lemma 4 of the note states that the only singular points of $V_\alpha$ are $(0,0)$ and $(\infty,\infty)$, both ordinary $m$-fold points; this is that clause, expressed through the four chart equations. The note assumes $|\alpha|=1$, which is not needed here.
--
--   **Formalization Note**: Each chart equation is a polynomial in two variables over $\mathbb{C}$, with the variables in the order written; multiplicities and tangent cones are computed chart by chart at complex points, and invariance under a change of chart is not claimed.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Lemma 4, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/OrdinaryMultiplePoints.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Mathlib.Algebra.MvPolynomial.Funext
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
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
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
open MvPolynomial

theorem CurveSymmetry.family_ordinary_multiple_points {m : ℕ} (hm : 2 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    OrdinaryAtOrigin (familyPolynomial m α) m ∧
      OrdinaryAtOrigin (familyInfinityPolynomial m α) m ∧
      (∀ x y : ℂ, planeEval x y (familyPolynomial m α) = 0 → ¬ (x = 0 ∧ y = 0) →
        HasMultiplicityAt (familyPolynomial m α) x y 1) ∧
      (∀ u v : ℂ, planeEval u v (familyInfinityPolynomial m α) = 0 → ¬ (u = 0 ∧ v = 0) →
        HasMultiplicityAt (familyInfinityPolynomial m α) u v 1) ∧
      (∀ u y : ℂ, planeEval u y (familyMixedPolynomial m α (star α)) = 0 →
        HasMultiplicityAt (familyMixedPolynomial m α (star α)) u y 1) ∧
      (∀ v x : ℂ, planeEval v x (familyMixedPolynomial m (star α) α) = 0 →
        HasMultiplicityAt (familyMixedPolynomial m (star α) α) v x 1) := by sorry
