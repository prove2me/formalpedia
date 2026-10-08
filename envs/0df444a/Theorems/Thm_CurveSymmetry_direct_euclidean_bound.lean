-- Prove2me | Theorems.Thm_CurveSymmetry_direct_euclidean_bound
-- name    : CurveSymmetry.direct_euclidean_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:32.356589+00:00
-- url     : https://prove2.me/theorems/7f354ac4-1aea-4a1d-a7fc-e22fef115070
-- title:
--   Finiteness of $\mathrm{Sym}^+(C)$ and the rotation bound $|\mathrm{Sym}^+(C)|\le\max\{d,2d-4\}$ for irreducible curves
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $P\in\mathbb C[X,Y]$ be irreducible in $\mathbb C[X,Y]$, of total degree $d=\deg P\ge 2$, and assume that its real locus $C=\{z\in\mathbb C: P(z,\bar z)=0\}$ is infinite and is not a circle: there are no $c\in\mathbb C$ and real $R>0$ with $C=\{z\in\mathbb C: |z-c|=R\}$. Let $\mathrm{Sym}^+(C)$ be the set of orientation-preserving isometries $T(z)=az+b$ ($a,b\in\mathbb C$, $|a|=1$) such that $T(z)\in C\iff z\in C$ for all $z\in\mathbb C$. Then $\mathrm{Sym}^+(C)$ is finite and
--
--   $$
--   |\mathrm{Sym}^+(C)|\le\max\{d,\,2d-4\}.
--   $$
--
--   This is the rotation bound of Theorem 1, together with the finiteness of $\mathrm{Sym}^+(C)$, for a curve given by an equation in $z$ and $\bar z$; no fixed center and no action on the equation are assumed. The version for a real Cartesian equation and the exact counts for the sharpness examples are derived from it.
--
--   **Formalization Note**: an isometry $T(z)=az+b$ is recorded by its pair $(a,b)\in\mathbb C\times\mathbb C$. The cardinality is the natural-number cardinality, which is $0$ for an infinite set, so finiteness is stated separately.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Theorem 1 (p. 1), Theorem 2 (p. 2), Lemma 3 (p. 2), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/DirectBound.lean (C. Perassi)

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

theorem CurveSymmetry.direct_euclidean_bound {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) (hcircle : NotCircle P) :
    Finite (DirectSymmetries P) ∧
      Nat.card (DirectSymmetries P) ≤ max P.totalDegree (2 * P.totalDegree - 4) := by sorry
