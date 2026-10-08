-- Prove2me | Theorems.Thm_CurveSymmetry_lineEquation_degree
-- name    : CurveSymmetry.lineEquation_degree
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:39.565699+00:00
-- url     : https://prove2.me/theorems/ef0b3ff8-0819-41ce-b303-21864a1e769d
-- title:
--   The complexified equation of a real line has total degree one
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=w$, $Y=\bar w$. For $z,v\in\mathbb C$ let $L_{z,v}(X,Y)=\bar v\,X-v\,Y-(\bar v z-v\bar z)\in\mathbb C[X,Y]$. Since $L_{z,v}(w,\bar w)=2i\operatorname{Im}\bigl(\bar v(w-z)\bigr)$, for $v\ne 0$ its real locus is the line through $z$ with direction $v$. If $v\ne 0$, then
--
--   $$
--   \deg L_{z,v}=1,
--   $$
--
--   that is, $L_{z,v}$ has total degree one.
--
--   It is used in the proof of Lemma 3, where lines (the orbit of a point under a translation, the fixed line of a reflection) are compared with an irreducible curve of degree at least two.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 3, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/Translation.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.lineEquation_degree (z v : ℂ) (hv : v ≠ 0) : (lineEquation z v).totalDegree = 1 := by sorry
