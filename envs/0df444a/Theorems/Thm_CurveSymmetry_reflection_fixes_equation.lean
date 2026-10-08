-- Prove2me | Theorems.Thm_CurveSymmetry_reflection_fixes_equation
-- name    : CurveSymmetry.reflection_fixes_equation
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:06.883875+00:00
-- url     : https://prove2.me/theorems/1e9a3a24-1826-4204-9578-1a6235662752
-- title:
--   A reflection in a line through the origin mapping the real locus into itself fixes the irreducible equation
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $P\in\mathbb C[X,Y]$ be irreducible in $\mathbb C[X,Y]$, of total degree $\deg P\ge 2$, with infinite real locus $C=\{z\in\mathbb C: P(z,\bar z)=0\}$. Let $a\in\mathbb C$ with $|a|=1$, and suppose that the reflection $z\mapsto a\bar z$ in a line through the origin maps $C$ into itself: $a\bar z\in C$ for every $z\in C$. Then the pullback of the equation by this reflection, given by the substitution $X\mapsto aY$, $Y\mapsto\bar a X$, is the equation itself:
--
--   $$
--   P(aY,\bar a X)=P(X,Y).
--   $$
--
--   This is the last clause of Lemma 3 for reflections in lines through the origin: a reflection preserving $C$ acts on the equation with sign $\varepsilon=1$, so it cannot negate it.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Theorem 1 (p. 1), Lemma 3 (p. 2), Remark 5 (p. 4), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/Reflection.lean (C. Perassi)

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

theorem CurveSymmetry.reflection_fixes_equation {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) {a : ℂ}
    (ha : ‖a‖ = 1) (hsym : ∀ z ∈ realLocus P, a * star z ∈ realLocus P) :
    reflect a P = P := by sorry
