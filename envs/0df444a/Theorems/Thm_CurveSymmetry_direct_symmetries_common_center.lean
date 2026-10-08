-- Prove2me | Theorems.Thm_CurveSymmetry_direct_symmetries_common_center
-- name    : CurveSymmetry.direct_symmetries_common_center
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:25.542486+00:00
-- url     : https://prove2.me/theorems/a543a15d-789b-4e87-897e-6ebb51557f23
-- title:
--   All orientation-preserving symmetries of an irreducible real locus of degree $\ge2$ fix a common point
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $P\in\mathbb C[X,Y]$ be irreducible in $\mathbb C[X,Y]$, of total degree $\deg P\ge 2$, with nonempty real locus $C=\{z\in\mathbb C: P(z,\bar z)=0\}$. Let $\mathrm{Sym}^+(C)$ be the set of orientation-preserving isometries $T(z)=az+b$ ($a,b\in\mathbb C$, $|a|=1$) such that $T(z)\in C\iff z\in C$ for all $z\in\mathbb C$. Then there is a point $z_0\in\mathbb C$ such that every $T(z)=az+b$ in $\mathrm{Sym}^+(C)$ satisfies
--
--   $$
--   b=(1-a)\,z_0,
--   $$
--
--   equivalently $T(z_0)=z_0$: every element of $\mathrm{Sym}^+(C)$ is a rotation about $z_0$ or the identity.
--
--   This is the step of the proof of Lemma 3 showing that all nonidentity rotations preserving $C$ have one center; it allows that center to be moved to the origin before equation (4) is applied.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 3, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/EuclideanCenter.lean (C. Perassi)

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

theorem CurveSymmetry.direct_symmetries_common_center {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty) :
    ∃ z : ℂ, ∀ a b : ℂ, DirectSymmetry (realLocus P) a b → b = (1 - a) * z := by sorry
