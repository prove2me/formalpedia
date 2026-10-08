-- Prove2me | Theorems.Thm_CurveSymmetry_opposite_symmetry_no_glide
-- name    : CurveSymmetry.opposite_symmetry_no_glide
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:47.029025+00:00
-- url     : https://prove2.me/theorems/3e5947e8-e711-42cd-b54b-676fd928ac43
-- title:
--   No glide reflections: a symmetry $z\mapsto a\bar z+b$ of an irreducible curve satisfies $a\bar b+b=0$
-- statement:
--   Let $P\in\mathbb{C}[X,Y]$ be irreducible, of total degree at least $2$, and let
--
--   $$S=\{z\in\mathbb{C} : P(z,\bar z)=0\}$$
--
--   be its real locus, written in the coordinates $X=z$, $Y=\bar z$. Assume $S\ne\varnothing$. Let $a,b\in\mathbb{C}$ with $|a|=1$, and suppose that the orientation-reversing isometry $T(z)=a\bar z+b$ preserves $S$, in the sense that $T(z)\in S\iff z\in S$ for every $z\in\mathbb{C}$.
--
--   Then
--
--   $$a\bar b+b=0.$$
--
--   Since $T(T(z))=z+a\bar b+b$, this says that $T\circ T$ is the identity: $T$ is not a glide reflection with nonzero translation part.
--
--   This is the exclusion of nontrivial glide reflections in the proof of Lemma 3 of the note. It is used to show that every orientation-reversing symmetry of $S$ fixes a point.
--
--   **Formalization Note**: No condition is imposed on the coefficients of $P$; in the note, $P$ comes from a real equation $f$ through $P(X,Y)=f\bigl((X+Y)/2,(X-Y)/(2i)\bigr)$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), proof of Lemma 3, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/IsometrySign.lean (C. Perassi)

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

theorem CurveSymmetry.opposite_symmetry_no_glide {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty) {a b : ℂ}
    (h : OppositeSymmetry (realLocus P) a b) : a * star b + b = 0 := by sorry
