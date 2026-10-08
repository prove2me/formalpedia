-- Prove2me | Theorems.Thm_CurveSymmetry_cartesianize_complexify
-- name    : CurveSymmetry.cartesianize_complexify
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:18.500391+00:00
-- url     : https://prove2.me/theorems/6d4fbe33-baef-45ae-b782-52e40fd5fb42
-- title:
--   Complexification followed by the Cartesian substitution is the identity of $\mathbb C[X,Y]$
-- statement:
--   For a polynomial $P\in\mathbb C[X,Y]$ define its complexification $P^{\mathbb C}(X,Y)=P\bigl(\tfrac{X+Y}{2},\tfrac{X-Y}{2i}\bigr)$ and its Cartesian substitution $P^{\mathrm{cart}}(X,Y)=P(X+iY,\,X-iY)$. The former rewrites a polynomial in the Cartesian coordinates $x=\tfrac{X+Y}{2}$, $y=\tfrac{X-Y}{2i}$ in terms of $X=z=x+iy$ and $Y=\bar z=x-iy$; the latter goes back. Both are $\mathbb C$-algebra endomorphisms of $\mathbb C[X,Y]$.
--
--   Then for every $P\in\mathbb C[X,Y]$,
--   $$\bigl(P^{\mathbb C}\bigr)^{\mathrm{cart}}=P,\qquad\text{that is,}\qquad P^{\mathbb C}(X+iY,\,X-iY)=P(X,Y).$$
--
--   Together with the reverse identity $\bigl(P^{\mathrm{cart}}\bigr)^{\mathbb C}=P$, this makes complexification an automorphism of $\mathbb C[X,Y]$ whose inverse is the Cartesian substitution. In the note a real equation $f(x,y)$ is rewritten, just before equation (4), as $P(X,Y)=f\bigl((X+Y)/2,(X-Y)/(2i)\bigr)$; being an automorphism, this substitution preserves irreducibility, which Lemma 3 and Theorems 1 and 2 rely on.
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

theorem CurveSymmetry.cartesianize_complexify (P : BPoly) : cartesianize (complexify P) = P := by sorry
