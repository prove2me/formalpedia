-- Prove2me | Theorems.Thm_CurveSymmetry_complexify_cartesianize
-- name    : CurveSymmetry.complexify_cartesianize
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:22.175976+00:00
-- url     : https://prove2.me/theorems/b0646f86-1446-40a7-a08e-73a3c4092239
-- title:
--   The Cartesian substitution followed by complexification is the identity of $\mathbb C[X,Y]$
-- statement:
--   For a polynomial $P\in\mathbb C[X,Y]$ let $P^{\mathrm{cart}}(X,Y)=P(X+iY,\,X-iY)$ be its Cartesian substitution and $P^{\mathbb C}(X,Y)=P\bigl(\tfrac{X+Y}{2},\tfrac{X-Y}{2i}\bigr)$ its complexification, which rewrites a polynomial in $x=\tfrac{X+Y}{2}$, $y=\tfrac{X-Y}{2i}$ in terms of $X=z=x+iy$ and $Y=\bar z=x-iy$. Both are $\mathbb C$-algebra endomorphisms of $\mathbb C[X,Y]$.
--
--   Then for every $P\in\mathbb C[X,Y]$,
--   $$\bigl(P^{\mathrm{cart}}\bigr)^{\mathbb C}=P,\qquad\text{that is,}\qquad P^{\mathrm{cart}}\Bigl(\frac{X+Y}{2},\,\frac{X-Y}{2i}\Bigr)=P(X,Y).$$
--
--   Together with the reverse identity $\bigl(P^{\mathbb C}\bigr)^{\mathrm{cart}}=P$, it shows that complexification, the passage made just before equation (4) of the note from a real equation $f(x,y)$ to $P(X,Y)=f\bigl((X+Y)/2,(X-Y)/(2i)\bigr)$, is an automorphism of $\mathbb C[X,Y]$. This direction is what allows an equation given in the coordinates $z,\bar z$ to be converted back into a Cartesian one, as in the descent to real Cartesian equations used for the examples of Theorems 1 and 2.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 2, equation (4), p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/CartesianCoordinates.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
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

theorem CurveSymmetry.complexify_cartesianize (P : BPoly) : complexify (cartesianize P) = P := by sorry
