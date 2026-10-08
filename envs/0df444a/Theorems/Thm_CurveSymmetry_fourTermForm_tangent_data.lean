-- Prove2me | Theorems.Thm_CurveSymmetry_fourTermForm_tangent_data
-- name    : CurveSymmetry.fourTermForm_tangent_data
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:27.280201+00:00
-- url     : https://prove2.me/theorems/467957ef-1b24-4d6f-b870-4a045e73e75e
-- title:
--   The lowest-degree part of $aX^m+bY^m+XY(cX^m+dY^m)$ is $aX^m+bY^m$, and $at^m+b$ is separable
-- statement:
--   Let $m\ge1$ be an integer, let $a,b\in\mathbb C$ be nonzero and $c,d\in\mathbb C$ arbitrary, and let $F(X,Y)=aX^m+bY^m+XY\,(cX^m+dY^m)\in\mathbb C[X,Y]$. For $n\ge0$ let $F_n$ be the homogeneous component of $F$ of degree $n$.
--
--   Then:
--
--   1. $F_n=0$ for every $n<m$;
--   2. $F_m=aX^m+bY^m$;
--   3. $aX^m+bY^m\ne0$;
--   4. the one-variable polynomial $at^m+b\in\mathbb C[t]$ is separable, i.e. it has $m$ distinct roots.
--
--   In short,
--   $$F_n=0\ \ (n<m),\qquad F_m=aX^m+bY^m\ne0,\qquad at^m+b\ \text{separable}.$$
--
--   So the origin is an $m$-fold point of $F=0$ whose tangent cone $aX^m+bY^m$ consists of $m$ distinct lines. Applied to $P_\alpha$, where $(a,b)=(\alpha,\bar\alpha)$, and to its equation $u^m+v^m+uv(\bar\alpha u^m+\alpha v^m)$ in the coordinates $u=1/X$, $v=1/Y$, it gives the tangent cones $\alpha X^m+\bar\alpha Y^m$ and $u^m+v^m$ of Lemma 4 at $(0,0)$ and $(\infty,\infty)$, both ordinary $m$-fold points.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 4, p. 3; Lemma 4, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyCharts.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
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

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.fourTermForm_tangent_data {m : ℕ} (hm : 0 < m) {a b : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (c d : ℂ) :
    (∀ n < m, homogeneousComponent n (fourTermForm m a b c d) = 0) ∧
      homogeneousComponent m (fourTermForm m a b c d) = binaryForm m a b ∧
      binaryForm m a b ≠ 0 ∧
      Polynomial.Separable (Polynomial.C a * Polynomial.X ^ m + Polynomial.C b) := by sorry
