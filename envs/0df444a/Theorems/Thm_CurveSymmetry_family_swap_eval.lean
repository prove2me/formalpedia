-- Prove2me | Theorems.Thm_CurveSymmetry_family_swap_eval
-- name    : CurveSymmetry.family_swap_eval
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:44.09521+00:00
-- url     : https://prove2.me/theorems/985f2797-7257-4c29-bf9e-ace799f5ded1
-- title:
--   Exchanging the two coordinates conjugates the parameter: $P_\beta(y,x)=P_{\bar\beta}(x,y)$
-- statement:
--   Let $m\ge0$ be an integer and, for $\gamma\in\mathbb C$, let $P_\gamma(X,Y)=X^m(\gamma+XY)+Y^m(\bar\gamma+XY)$ be the polynomial of equation (6). Let $\beta\in\mathbb C$.
--
--   Then for all $x,y\in\mathbb C$,
--   $$P_\beta(y,x)=P_{\bar\beta}(x,y).$$
--
--   An anti-Möbius map $M\circ\mathrm{conj}$ acts on the complex coordinates $X=z$, $Y=\bar z$ by $(X,Y)\mapsto(M(Y),\overline M(X))$, exchanging the roles of the two coordinates. This identity reduces the antiholomorphic cases $z\mapsto c\bar z$ and $z\mapsto c/\bar z$ in the proof of Theorem 2 to the holomorphic ones with $\beta$ replaced by $\bar\beta$, as reflected in the ratios (8).
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

theorem CurveSymmetry.family_swap_eval (m : ℕ) (β x y : ℂ) :
    planeEval y x (familyPolynomial m β) = planeEval x y (familyPolynomial m (star β)) := by sorry
