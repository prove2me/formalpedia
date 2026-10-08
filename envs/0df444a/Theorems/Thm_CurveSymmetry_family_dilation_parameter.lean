-- Prove2me | Theorems.Thm_CurveSymmetry_family_dilation_parameter
-- name    : CurveSymmetry.family_dilation_parameter
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:39.642716+00:00
-- url     : https://prove2.me/theorems/aaf9d087-27e9-4e93-a0d7-bec0a9706a5f
-- title:
--   Dilation pullback: $P_\beta(cX,\bar cY)=k\,P_\alpha$, $|\alpha|=|\beta|=1$, forces $|c|=1$ and $\beta=\alpha$
-- statement:
--   Let $m\ge1$ be an integer and let $\alpha,\beta,c,k\in\mathbb C$ with $|\alpha|=|\beta|=1$ and $c\ne0$. For $\gamma\in\mathbb C$ let $P_\gamma(X,Y)=X^m(\gamma+XY)+Y^m(\bar\gamma+XY)$ be the polynomial of equation (6). The dilation $z\mapsto cz$ acts on the complex coordinates $X=z$, $Y=\bar z$ by $X\mapsto cX$, $Y\mapsto\bar cY$.
--
--   Suppose that the pullback of $P_\beta$ under this dilation is a multiple of $P_\alpha$:
--   $$P_\beta(cX,\bar cY)=k\,P_\alpha(X,Y)\qquad\text{in }\mathbb C[X,Y].$$
--   Then $|c|=1$ and $\beta=\alpha$.
--
--   This is the case $z\mapsto cz$ of the coefficient-ratio comparison (8) in the proof of Theorem 2, where the ratio is $\beta/|c|^2$: such a dilation must be a rotation and cannot change a parameter of modulus one.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Theorem 2, equation (8), p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyTransport.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
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

theorem CurveSymmetry.family_dilation_parameter {m : ℕ} (hm : 0 < m) {α β c k : ℂ}
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (hc : c ≠ 0)
    (he : dilate c (familyPolynomial m β) = C k * familyPolynomial m α) :
    ‖c‖ = 1 ∧ β = α := by sorry
