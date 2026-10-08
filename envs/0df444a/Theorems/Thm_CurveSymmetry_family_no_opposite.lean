-- Prove2me | Theorems.Thm_CurveSymmetry_family_no_opposite
-- name    : CurveSymmetry.family_no_opposite
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:36.424615+00:00
-- url     : https://prove2.me/theorems/21cc1967-fc6b-41fa-b408-d68f416dd75e
-- title:
--   For $m\ge3$ the curve $C_{m,\alpha}$ has no orientation-reversing Euclidean symmetry
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $m\ge 3$ be an integer and let $\alpha\in\mathbb C$ be nonreal, $\alpha\ne\bar\alpha$; the condition $|\alpha|=1$ of the note is not required. Let $C_{m,\alpha}=\{z\in\mathbb C: P_\alpha(z,\bar z)=0\}$ be the real locus of $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$, that is, the curve $\operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0$. Then $C_{m,\alpha}$ has no orientation-reversing Euclidean symmetry: there are no $a,b\in\mathbb C$ with $|a|=1$ such that
--
--   $$
--   a\bar z+b\in C_{m,\alpha}\iff z\in C_{m,\alpha}\qquad\text{for all }z\in\mathbb C.
--   $$
--
--   For $m\ge 3$, that is in degree $m+2\ge 5$, this gives the Euclidean clause of Theorem 2: together with the count of $2m$ orientation-preserving symmetries, $\mathrm{Sym}(C_{m,\alpha})$ consists exactly of the $2m$ rotations $z\mapsto cz$ with $c^{2m}=1$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Theorem 2, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyRotations.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic
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

theorem CurveSymmetry.family_no_opposite {m : ℕ} (hm : 3 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    IsEmpty (OppositeSymmetries (familyPolynomial m α)) := by sorry
