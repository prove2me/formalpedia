-- Prove2me | Theorems.Thm_CurveSymmetry_direct_bound_with_opposite
-- name    : CurveSymmetry.direct_bound_with_opposite
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:21.840901+00:00
-- url     : https://prove2.me/theorems/e58b8c7a-6d75-4e76-8b30-3756a5882776
-- title:
--   An orientation-reversing symmetry forces $|\mathrm{Sym}^+(C)|\le d$
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $P\in\mathbb C[X,Y]$ be irreducible in $\mathbb C[X,Y]$, of total degree $d=\deg P\ge 2$, and assume that its real locus $C=\{z\in\mathbb C: P(z,\bar z)=0\}$ is infinite and is not a circle: there are no $c\in\mathbb C$ and real $R>0$ with $C=\{z\in\mathbb C: |z-c|=R\}$. Let $\mathrm{Sym}^+(C)$ be the set of orientation-preserving isometries $T(z)=az+b$ ($a,b\in\mathbb C$, $|a|=1$) such that $T(z)\in C\iff z\in C$ for all $z\in\mathbb C$. Suppose that $C$ has an orientation-reversing symmetry, that is, there are $a_0,b_0\in\mathbb C$ with $|a_0|=1$ and $a_0\bar z+b_0\in C\iff z\in C$ for all $z\in\mathbb C$. Then
--
--   $$
--   |\mathrm{Sym}^+(C)|\le d.
--   $$
--
--   In the proof of Theorem 1 this is the case in which $C$ has a reflection; it gives $N\le d$ and hence $|\mathrm{Sym}(C)|\le 2d$. In the formalization it is also used to exclude orientation-reversing symmetries of the curves $C_{m,\alpha}$ of equation (1) with $m\ge 3$, and to count the symmetries of the curves $\operatorname{Re}(z^d)=1$.
--
--   **Formalization Note**: isometries are recorded by their pairs $(a,b)\in\mathbb C\times\mathbb C$, and the orientation-reversing symmetry is given as such a pair. The cardinality is the natural-number cardinality, which is $0$ for an infinite set; the finiteness of $\mathrm{Sym}^+(C)$ is a separate result.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Theorem 1 (p. 1), Lemma 3 (p. 2), Remark 5 (p. 4), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/ReflectionBound.lean (C. Perassi)

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

theorem CurveSymmetry.direct_bound_with_opposite {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) (hcircle : NotCircle P)
    (g : OppositeSymmetries P) : Nat.card (DirectSymmetries P) ≤ P.totalDegree := by sorry
