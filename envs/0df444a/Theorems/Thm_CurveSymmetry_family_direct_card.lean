-- Prove2me | Theorems.Thm_CurveSymmetry_family_direct_card
-- name    : CurveSymmetry.family_direct_card
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:53.20716+00:00
-- url     : https://prove2.me/theorems/6e30c80e-42b8-4a9b-abbf-177581ba3cfa
-- title:
--   For $m\ge2$ the curve $C_{m,\alpha}$ has exactly $2m$ orientation-preserving symmetries
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $m\ge 2$ be an integer and let $\alpha\in\mathbb C$ be nonreal, $\alpha\ne\bar\alpha$; the condition $|\alpha|=1$ of the note is not required. Let $C_{m,\alpha}=\{z\in\mathbb C: P_\alpha(z,\bar z)=0\}$ be the real locus of $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$, that is, the curve $\operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0$. Let $\mathrm{Sym}^+(C_{m,\alpha})$ be the set of orientation-preserving isometries $T(z)=az+b$ ($a,b\in\mathbb C$, $|a|=1$) such that $T(z)\in C_{m,\alpha}\iff z\in C_{m,\alpha}$ for all $z\in\mathbb C$. Then
--
--   $$
--   |\mathrm{Sym}^+(C_{m,\alpha})|=2m.
--   $$
--
--   Since $P_\alpha$ has degree $d=m+2$, the count $2m=2d-4$ shows that the rotation bound $\max\{d,2d-4\}$ of Theorem 1 is attained in every degree $d\ge 4$, and it is used for the converse clause of Theorem 1; it is also the rotation count of Theorem 2. For $m=2$ it concerns the degree-four members of the family, which Remark 5 compares with the curve $\operatorname{Re}(z^4)=1$.
--
--   **Formalization Note**: isometries are recorded by their pairs $(a,b)\in\mathbb C\times\mathbb C$, and the cardinality is the natural-number cardinality; since $2m>0$, the equality includes the finiteness of $\mathrm{Sym}^+(C_{m,\alpha})$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyRotations.lean (C. Perassi)

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

theorem CurveSymmetry.family_direct_card {m : ℕ} (hm : 2 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    Nat.card (DirectSymmetries (familyPolynomial m α)) = 2 * m := by sorry
