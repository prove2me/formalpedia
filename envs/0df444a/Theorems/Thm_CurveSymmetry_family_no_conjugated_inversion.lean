-- Prove2me | Theorems.Thm_CurveSymmetry_family_no_conjugated_inversion
-- name    : CurveSymmetry.family_no_conjugated_inversion
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:27.056669+00:00
-- url     : https://prove2.me/theorems/edb57656-333c-4c68-98da-d7877b6b0e52
-- title:
--   No map $z\mapsto c/z$ pulls $P_{\bar\alpha}$ back to a multiple of $P_\alpha$ if $|\alpha|=1$, $\alpha\notin\mathbb R$
-- statement:
--   Let $m\ge1$ be an integer, let $\alpha\in\mathbb C$ with $|\alpha|=1$ and $\alpha\notin\mathbb R$, let $c\in\mathbb C$ with $c\ne0$, and let $k\in\mathbb C$ be arbitrary. For $\gamma\in\mathbb C$ let $P_\gamma(X,Y)=X^m(\gamma+XY)+Y^m(\bar\gamma+XY)$ be the polynomial of equation (6). The map $z\mapsto c/z$ acts on the complex coordinates $X=z$, $Y=\bar z$ by $(X,Y)\mapsto(c/X,\bar c/Y)$; clearing the denominator of the pullback of $P_{\bar\alpha}$ gives $I_{\bar\alpha,c}(X,Y)=(XY)^{m+1}P_{\bar\alpha}(c/X,\bar c/Y)=\bar c^{m}|c|^2X^m+c^m|c|^2Y^m+XY\bigl(\bar c^{m}\alpha X^m+c^m\bar\alpha Y^m\bigr)$.
--
--   Then this polynomial is not a multiple of $P_\alpha$:
--   $$I_{\bar\alpha,c}\ne k\,P_\alpha\qquad\text{in }\mathbb C[X,Y].$$
--
--   By the coordinate exchange $P_\alpha(y,x)=P_{\bar\alpha}(x,y)$, the cleared pullback of $P_\alpha$ under the antiholomorphic map $z\mapsto c/\bar z$, which acts by $(X,Y)\mapsto(c/Y,\bar c/X)$, is $I_{\bar\alpha,\bar c}$. So this is the polynomial fact used in the proof of Theorem 2 to exclude anti-Möbius self-equivalences of $\widehat C_{m,\alpha}$ of the form $z\mapsto c/\bar z$.
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

theorem CurveSymmetry.family_no_conjugated_inversion {m : ℕ} (hm : 0 < m) {α c k : ℂ}
    (hα : ‖α‖ = 1) (ha : α ≠ star α) (hc : c ≠ 0) :
    inversionFamily m (star α) c ≠ C k * familyPolynomial m α := by sorry
