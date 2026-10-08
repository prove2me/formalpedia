-- Prove2me | Theorems.Thm_CurveSymmetry_linear_substitution_degree_le
-- name    : CurveSymmetry.linear_substitution_degree_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:40.165351+00:00
-- url     : https://prove2.me/theorems/aeb8c78f-a804-4465-940d-b09077403921
-- title:
--   Substituting polynomials of degree at most one does not increase the total degree
-- statement:
--   Let $v_0,v_1\in\mathbb C[X,Y]$ be polynomials of total degree at most $1$ (affine-linear polynomials, constants allowed), let $P\in\mathbb C[X,Y]$, and write $P(v_0,v_1)$ for the polynomial obtained by substituting $v_0$ for $X$ and $v_1$ for $Y$.
--
--   Then
--   $$\deg P(v_0,v_1)\le\deg P,$$
--   where $\deg$ denotes the total degree.
--
--   Applied to the two mutually inverse substitutions $(X,Y)\mapsto\bigl(\tfrac{X+Y}{2},\tfrac{X-Y}{2i}\bigr)$ and $(X,Y)\mapsto(X+iY,\,X-iY)$, it shows that the complexification $P(X,Y)=f\bigl((X+Y)/2,(X-Y)/(2i)\bigr)$ of a Cartesian equation $f$ has the same total degree $d$ as $f$; this is the degree count behind the expansion $P=\sum_{a+b\le d}p_{ab}X^aY^b$ before equation (4) of the note.
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

theorem CurveSymmetry.linear_substitution_degree_le (v : Fin 2 → BPoly) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (P : BPoly) : (eval₂Hom C v P).totalDegree ≤ P.totalDegree := by sorry
