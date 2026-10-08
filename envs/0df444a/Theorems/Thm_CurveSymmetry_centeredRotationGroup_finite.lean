-- Prove2me | Theorems.Thm_CurveSymmetry_centeredRotationGroup_finite
-- name    : CurveSymmetry.centeredRotationGroup_finite
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:33.557191+00:00
-- url     : https://prove2.me/theorems/8af4cbb6-b787-4dd0-9c4b-0b3cf2a34611
-- title:
--   Finitely many rotations about the origin preserve an infinite irreducible real locus other than a centered circle
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $P\in\mathbb C[X,Y]$ be irreducible in $\mathbb C[X,Y]$, with infinite real locus $C=\{z\in\mathbb C: P(z,\bar z)=0\}$, and assume that $C$ is not a circle centered at the origin: there is no real $R>0$ with $C=\{z\in\mathbb C: |z|=R\}$. Let
--
--   $$
--   G=\bigl\{u\in\mathbb C^\times : |u|=1 \text{ and } \bigl(uz\in C\iff z\in C\bigr) \text{ for all } z\in\mathbb C\bigr\}
--   $$
--
--   be the group of rotations about the origin that preserve $C$. Then $G$ is finite.
--
--   This is the finiteness of the rotations about a fixed center, which enters the finiteness clause of Lemma 3. In the formalization it is used to bound the orientation-preserving symmetries of $C$ when an orientation-reversing one exists.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Theorem 1 (p. 1), Theorem 2 (p. 2), Lemma 3 (p. 2), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/RotationGroup.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.centeredRotationGroup_finite {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R) :
    Finite (centeredRotationGroup P) := by sorry
