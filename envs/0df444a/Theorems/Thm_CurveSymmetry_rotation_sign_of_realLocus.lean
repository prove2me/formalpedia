-- Prove2me | Theorems.Thm_CurveSymmetry_rotation_sign_of_realLocus
-- name    : CurveSymmetry.rotation_sign_of_realLocus
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:07.901383+00:00
-- url     : https://prove2.me/theorems/2ed1c3bc-8079-43c9-9a8d-1ecfad61296f
-- title:
--   A rotation about the origin mapping the real locus into itself fixes the irreducible equation up to sign
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $P\in\mathbb C[X,Y]$ be irreducible in $\mathbb C[X,Y]$, with infinite real locus $C=\{z\in\mathbb C: P(z,\bar z)=0\}$. Let $\zeta\in\mathbb C$ with $|\zeta|=1$, not necessarily a root of unity, and suppose that the rotation $z\mapsto\zeta z$ maps $C$ into itself: $\zeta z\in C$ for every $z\in C$. Then
--
--   $$
--   P(\zeta X,\zeta^{-1}Y)=P(X,Y)\qquad\text{or}\qquad P(\zeta X,\zeta^{-1}Y)=-P(X,Y).
--   $$
--
--   Since $\zeta^{-1}=\bar\zeta$, the left-hand side is the pullback of the equation by the rotation. This is the sign clause of Lemma 3 for rotations about the origin, in the form of equation (4).
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 2, equation (4), p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/GeometricRotation.lean (C. Perassi)

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

theorem CurveSymmetry.rotation_sign_of_realLocus {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) {ζ : ℂ} (hnorm : ‖ζ‖ = 1)
    (hsym : ∀ z ∈ realLocus P, ζ * z ∈ realLocus P) :
    rotate ζ P = P ∨ rotate ζ P = -P := by sorry
