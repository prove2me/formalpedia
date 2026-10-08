-- Prove2me | Theorems.Thm_CurveSymmetry_fourTermForm_singular_iff
-- name    : CurveSymmetry.fourTermForm_singular_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:51.554147+00:00
-- url     : https://prove2.me/theorems/908f855e-2e2f-46c0-8c35-8cca4379c3b9
-- title:
--   The origin is the only affine singular point of $aX^m+bY^m+XY(cX^m+dY^m)$ when $ab(ad-bc)\ne0$
-- statement:
--   Let $m\ge2$ be an integer and let $a,b,c,d\in\mathbb C$ with $a\ne0$, $b\ne0$ and $ad-bc\ne0$. Consider $F(X,Y)=aX^m+bY^m+XY\,(cX^m+dY^m)\in\mathbb C[X,Y]$, and call a point $(x,y)\in\mathbb C^2$ singular for $F$ if $F$ and both of its partial derivatives vanish there.
--
--   Then for every $(x,y)\in\mathbb C^2$,
--   $$F(x,y)=\frac{\partial F}{\partial X}(x,y)=\frac{\partial F}{\partial Y}(x,y)=0\iff(x,y)=(0,0).$$
--
--   With $(a,b,c,d)=(\alpha,\bar\alpha,1,1)$ the polynomial $F$ is $P_\alpha$, and in the coordinates $u=1/X$, $v=1/Y$ the equation of $V_\alpha$ near $(\infty,\infty)$ is $u^m+v^m+uv(\bar\alpha u^m+\alpha v^m)$, of the same shape; in both cases $ad-bc=\alpha-\bar\alpha\ne0$ when $\alpha\notin\mathbb R$. This gives the part of Lemma 4 locating the singular points of $V_\alpha$ in these two charts.
--
--   **Formalization Note**: the partial derivatives are formal derivatives of polynomials, and only points of the affine plane $\mathbb C^2$ are concerned.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 4, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilySingularities.lean (C. Perassi)

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

theorem CurveSymmetry.fourTermForm_singular_iff {m : ℕ} (hm : 2 ≤ m) {a b c d x y : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hdet : a * d - b * c ≠ 0) :
    JacobianSingular (fourTermForm m a b c d) x y ↔ x = 0 ∧ y = 0 := by sorry
