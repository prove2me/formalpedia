-- Prove2me | Theorems.Thm_CurveSymmetry_paper_high_order_radial_form
-- name    : CurveSymmetry.paper_high_order_radial_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:45:03.997+00:00
-- url     : https://prove2.me/theorems/8b25087f-11a1-4f0e-91c9-fb9cf6eac999
-- title:
--   Equation (5): a rotation of order $N>d$ forces $N=2m$ and $P=X^mA(XY)+Y^m\bar A(XY)$ with $A$ nonconstant
-- statement:
--   Let $f\in\mathbb R[x,y]$ be a polynomial that is irreducible in $\mathbb C[x,y]$, of total degree $d\ge 2$, and let $C=\{z\in\mathbb C:\ f(\operatorname{Re}z,\operatorname{Im}z)=0\}$ be its real zero set. Assume that $C$ is infinite and is not a circle: $C\ne\{z\in\mathbb C:\ |z-c|=R\}$ for all $c\in\mathbb C$ and all real $R>0$. Let $P(X,Y)=f\big((X+Y)/2,(X-Y)/(2i)\big)\in\mathbb C[X,Y]$ be $f$ written in the coordinates $X=z$, $Y=\bar z$. Finally, let $N$ be a natural number with $N>d$, and let $\zeta\in\mathbb C$ be a primitive $N$-th root of unity such that the rotation $z\mapsto\zeta z$ maps $C$ into itself.
--
--   Then there are a natural number $m$ and a polynomial $A\in\mathbb C[s]$ such that
--
--   $$
--   P(X,Y)=X^m\,A(XY)+Y^m\,\overline{A}(XY),
--   $$
--
--   where $\overline{A}$ is obtained from $A$ by conjugating its coefficients, and moreover:
--
--   1. $N=2m$;
--   2. $P(\zeta X,\zeta^{-1}Y)=-P(X,Y)$;
--   3. $1\le\deg A\le\lfloor (d-m)/2\rfloor$;
--   4. $m+2\le d$.
--
--   This is equation (5) of the note, in the case of the proof of Theorem 1 where the rotation group has order $N>d$ (after the center of rotation has been moved to the origin): the order is even, the sign in equation (4) is $-1$, and $P$ has the radial form (5) with $A$ nonconstant. The inequality $m\le d-2$ then gives $N\le 2d-4$.
--
--   **Formalization Note**: the curve $C$ is a subset of $\mathbb C$, and the rotation is only assumed to map $C$ into $C$, not onto it.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), proof of Theorem 1, equation (5), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/RadialAntiForm.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
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

theorem CurveSymmetry.paper_high_order_radial_form {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R)
    {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (hN : f.totalDegree < N)
    (hsym : ∀ z ∈ cartesianLocus f, ζ * z ∈ cartesianLocus f) :
    ∃ m : ℕ, N = 2 * m ∧ rotate ζ (complexifyReal f) = -complexifyReal f ∧
      ∃ A : Polynomial ℂ,
        complexifyReal f = (X 0 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) A +
          (X 1 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) (A.map (starRingEnd ℂ)) ∧
        1 ≤ A.natDegree ∧ A.natDegree ≤ (f.totalDegree - m) / 2 ∧ m + 2 ≤ f.totalDegree := by sorry
