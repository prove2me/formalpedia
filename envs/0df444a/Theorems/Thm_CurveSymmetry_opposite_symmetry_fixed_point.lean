-- Prove2me | Theorems.Thm_CurveSymmetry_opposite_symmetry_fixed_point
-- name    : CurveSymmetry.opposite_symmetry_fixed_point
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:43.226537+00:00
-- url     : https://prove2.me/theorems/a2293843-3ff8-4de8-9c4f-bec63fa6061a
-- title:
--   An orientation-reversing symmetry $z\mapsto a\bar z+b$ of an irreducible curve fixes the point $b/2$
-- statement:
--   Let $P\in\mathbb{C}[X,Y]$ be irreducible, of total degree at least $2$, and let
--
--   $$S=\{z\in\mathbb{C} : P(z,\bar z)=0\}$$
--
--   be its real locus, written in the coordinates $X=z$, $Y=\bar z$. Assume $S\ne\varnothing$. Let $a,b\in\mathbb{C}$ with $|a|=1$, and suppose that the orientation-reversing isometry $T(z)=a\bar z+b$ preserves $S$, in the sense that $T(z)\in S\iff z\in S$ for every $z\in\mathbb{C}$.
--
--   Then $T$ fixes the point $b/2$:
--
--   $$T(b/2)=a\,\overline{(b/2)}+b=\frac{b}{2}.$$
--
--   An orientation-reversing isometry of the plane with a fixed point is the reflection in a line through that point, so every orientation-reversing symmetry of $S$ is a reflection. In the proof of Lemma 3 of the note this is why the clause about reflections covers all orientation-reversing symmetries; it is used for the sign statement of Lemma 3.
--
--   **Formalization Note**: No condition is imposed on the coefficients of $P$.
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

theorem CurveSymmetry.opposite_symmetry_fixed_point {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty) {a b : ℂ}
    (h : OppositeSymmetry (realLocus P) a b) : a * star (b / 2) + b = b / 2 := by sorry
