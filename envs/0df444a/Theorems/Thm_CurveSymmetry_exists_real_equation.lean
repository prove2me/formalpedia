-- Prove2me | Theorems.Thm_CurveSymmetry_exists_real_equation
-- name    : CurveSymmetry.exists_real_equation
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:21.128255+00:00
-- url     : https://prove2.me/theorems/ff51b310-43c6-4ba0-9f5a-df3d9c73ec3d
-- title:
--   An irreducible equation with infinite real locus rescales to one with conjugate-symmetric coefficients
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $P\in\mathbb C[X,Y]$ be irreducible in $\mathbb C[X,Y]$, of total degree $\deg P\ge 2$, with infinite real locus $C=\{z\in\mathbb C: P(z,\bar z)=0\}$. Then there is a constant $c\in\mathbb C$, $c\ne 0$, such that the coefficients of $cP=\sum_{a,b\ge 0}q_{ab}X^aY^b$ are conjugate-symmetric:
--
--   $$
--   q_{ba}=\overline{q_{ab}}\qquad\text{for all }a,b\ge 0.
--   $$
--
--   Conjugate-symmetric coefficients are those of the complexification $f\bigl((X+Y)/2,(X-Y)/(2i)\bigr)$ of a real polynomial $f(x,y)$, as in the symmetry $p_{ba}=\overline{p_{ab}}$ stated before equation (4). The lemma is used to recover a real Cartesian equation for $C$, which connects the statements in the coordinates $z,\bar z$ with the setting of Theorems 1 and 2.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 2, equation (4), p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/RealEquation.lean (C. Perassi)

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

theorem CurveSymmetry.exists_real_equation {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ a b : ℕ,
      (C c * P).coeff (exponent b a) = star ((C c * P).coeff (exponent a b)) := by sorry
