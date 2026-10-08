-- Prove2me | Theorems.Thm_CurveSymmetry_no_translation_symmetry
-- name    : CurveSymmetry.no_translation_symmetry
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:45.160848+00:00
-- url     : https://prove2.me/theorems/0da72f79-d9cc-4310-bd61-233bd0ad8c94
-- title:
--   No nonzero translation maps an irreducible real locus of degree $\ge2$ into itself
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $P\in\mathbb C[X,Y]$ be irreducible in $\mathbb C[X,Y]$, of total degree $\deg P\ge 2$, with nonempty real locus $C=\{z\in\mathbb C: P(z,\bar z)=0\}$. Let $v\in\mathbb C$ be such that the translation $z\mapsto z+v$ maps $C$ into itself: $z+v\in C$ for every $z\in C$. Then
--
--   $$
--   v=0.
--   $$
--
--   This is the exclusion of nonzero translations in the proof of Lemma 3. In the formalization it is used to show that the orientation-preserving symmetries of $C$ have a common center, that $C$ has no glide reflection, and that every symmetry of $C$ acts on the equation by a sign.
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

theorem CurveSymmetry.no_translation_symmetry {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty) {v : ℂ}
    (htrans : ∀ z ∈ realLocus P, z + v ∈ realLocus P) : v = 0 := by sorry
