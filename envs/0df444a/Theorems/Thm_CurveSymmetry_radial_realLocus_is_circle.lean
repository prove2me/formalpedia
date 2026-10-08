-- Prove2me | Theorems.Thm_CurveSymmetry_radial_realLocus_is_circle
-- name    : CurveSymmetry.radial_realLocus_is_circle
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:08.205539+00:00
-- url     : https://prove2.me/theorems/b1f07c38-fcc3-4dd5-adcd-8cd7f73c4ac8
-- title:
--   An infinite real locus of $c\,(XY-r)$ is a circle centered at the origin
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $c,r\in\mathbb C$ with $c\ne 0$, let $P=c\,(XY-r)\in\mathbb C[X,Y]$, and let $C=\{z\in\mathbb C: P(z,\bar z)=0\}$ be its real locus, that is, the set of $z$ with $|z|^2=r$. If $C$ is infinite, then there is a real number $R>0$ such that
--
--   $$
--   C=\{z\in\mathbb C: |z|=R\}.
--   $$
--
--   In the proof of Theorem 1 this is the step at which an irreducible radial equation with infinite real locus is seen to define a circle, a case excluded by the hypotheses of Theorem 1.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Theorem 1, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/RealLocus.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.radial_realLocus_is_circle {P : BPoly}
    (hinf : (realLocus P).Infinite)
    (hform : ∃ a r : ℂ, a ≠ 0 ∧ P = C a * ((X 0 : BPoly) * X 1 - C r)) :
    ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R := by sorry
