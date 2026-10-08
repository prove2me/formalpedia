-- Prove2me | Theorems.Thm_CurveSymmetry_family_point_of_norm
-- name    : CurveSymmetry.family_point_of_norm
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:57.172881+00:00
-- url     : https://prove2.me/theorems/2dcd496a-0279-466f-9e2a-6fb7cc338590
-- title:
--   The curve $C_{m,\alpha}$ has a point of every modulus $r\ge0$
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $m\ge 1$ be an integer and let $\alpha\in\mathbb C$ be nonreal, $\alpha\ne\bar\alpha$; the condition $|\alpha|=1$ of the note is not required. Let $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$ be the polynomial of equation (6), and let $C_{m,\alpha}=\{z\in\mathbb C: P_\alpha(z,\bar z)=0\}$ be its real locus, the curve $\operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0$ of equation (1). Then $C_{m,\alpha}$ meets every circle about the origin, including the degenerate one of radius $0$: for every real $r\ge 0$ there is $z\in\mathbb C$ with
--
--   $$
--   z\in C_{m,\alpha}\qquad\text{and}\qquad |z|=r.
--   $$
--
--   In the formalization this yields that $C_{m,\alpha}$ is infinite, as stated in Lemma 4, and that it is not a circle; it also enters the count of the $2m$ points of $C_{m,\alpha}$ on each circle $|z|=r>0$ in the proof of Lemma 4.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Theorem 1 (p. 1), Theorem 2 (p. 2), Lemma 4 (p. 3), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyRealLocus.lean (C. Perassi)

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

theorem CurveSymmetry.family_point_of_norm {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α)
    {r : ℝ} (hr : 0 ≤ r) : ∃ z ∈ realLocus (familyPolynomial m α), ‖z‖ = r := by sorry
