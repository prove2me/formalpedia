-- Prove2me | Theorems.Thm_CurveSymmetry_exists_cartesian_equation
-- name    : CurveSymmetry.exists_cartesian_equation
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:32.113024+00:00
-- url     : https://prove2.me/theorems/24ac3907-7579-4dc9-ae4a-f37e70752626
-- title:
--   Descent from an irreducible equation in $z,\bar z$ to a real Cartesian equation with the same curve and degree
-- statement:
--   Let $P=\sum p_{ab}X^aY^b\in\mathbb C[X,Y]$ be irreducible and of total degree at least $2$, and suppose that its real locus $\{z\in\mathbb C: P(z,\bar z)=0\}$, the curve that $P$ defines in the complex coordinates $X=z$, $Y=\bar z$, is infinite. No condition is imposed on the coefficients of $P$; in particular the symmetry $p_{ba}=\overline{p_{ab}}$ of a complexified real equation is not assumed.
--
--   Then there is a polynomial $f\in\mathbb R[x,y]$, irreducible in $\mathbb C[x,y]$, with $\deg f=\deg P$ (total degrees), whose real zero set is that curve:
--   $$\{z\in\mathbb C: f(\operatorname{Re}z,\operatorname{Im}z)=0\}=\{z\in\mathbb C: P(z,\bar z)=0\}.$$
--
--   It lets curves constructed in the coordinates $z,\bar z$ be presented by real Cartesian equations, the setting of Theorem 1. It is used for the sharpness examples and the converse of the equality case in Theorem 1, and for the statement in Theorem 2 that $C_{m,\alpha}$ is an infinite geometrically irreducible curve of degree $m+2$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Theorem 1, sharpness examples, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/CartesianDescent.lean (C. Perassi)

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

theorem CurveSymmetry.exists_cartesian_equation {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = P.totalDegree ∧
      cartesianLocus f = realLocus P := by sorry
