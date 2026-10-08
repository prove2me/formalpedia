-- Prove2me | Theorems.Thm_CurveSymmetry_family_inversion_parameter
-- name    : CurveSymmetry.family_inversion_parameter
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:58.452753+00:00
-- url     : https://prove2.me/theorems/32183ee8-2871-43bd-8b4b-044276035bb0
-- title:
--   Inversion pullback: $(XY)^{m+1}P_\beta(c/X,\bar c/Y)=k\,P_\alpha$, $|\alpha|=|\beta|=1$, forces $|c|=1$, $\beta=\alpha$
-- statement:
--   Let $m\ge1$ be an integer and let $\alpha,\beta,c,k\in\mathbb C$ with $|\alpha|=|\beta|=1$ and $c\ne0$. For $\gamma\in\mathbb C$ let $P_\gamma(X,Y)=X^m(\gamma+XY)+Y^m(\bar\gamma+XY)$ be the polynomial of equation (6). The map $z\mapsto c/z$ acts on the complex coordinates $X=z$, $Y=\bar z$ by $(X,Y)\mapsto(c/X,\bar c/Y)$; clearing the denominator $(XY)^{m+1}$ of the pulled-back equation gives the polynomial $I_{\beta,c}(X,Y)=(XY)^{m+1}P_\beta(c/X,\bar c/Y)=\bar c^{m}|c|^2X^m+c^m|c|^2Y^m+XY\bigl(\bar c^{m}\bar\beta X^m+c^m\beta Y^m\bigr)$.
--
--   Suppose that this polynomial is a multiple of $P_\alpha$:
--   $$I_{\beta,c}=k\,P_\alpha\qquad\text{in }\mathbb C[X,Y].$$
--   Then $|c|=1$ and $\beta=\alpha$.
--
--   This is the case $z\mapsto c/z$ of the coefficient-ratio comparison (8) in the proof of Theorem 2, where the ratio is $|c|^2/\bar\beta$: such a map must have $|c|=1$ and cannot change a parameter of modulus one.
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

theorem CurveSymmetry.family_inversion_parameter {m : ℕ} (hm : 0 < m) {α β c k : ℂ}
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (hc : c ≠ 0)
    (he : inversionFamily m β c = C k * familyPolynomial m α) :
    ‖c‖ = 1 ∧ β = α := by sorry
