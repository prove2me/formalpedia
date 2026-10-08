-- Prove2me | Theorems.Thm_CurveSymmetry_normalize_twoParameter
-- name    : CurveSymmetry.normalize_twoParameter
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:43.847092+00:00
-- url     : https://prove2.me/theorems/d4d49d2f-e659-499b-b9dc-55c61198e555
-- title:
--   Normalizing $X^m(a+bXY)+Y^m(\bar a+\bar bXY)$ to a positive multiple of $P_\alpha$ by a dilation $z\mapsto cz$
-- statement:
--   Let $m\ge1$ be an integer and let $a,b\in\mathbb C$ with $b\ne0$ and $a/b\notin\mathbb R$ (that is, $a/b\ne\overline{a/b}$). Work in $\mathbb C[X,Y]$, where $X$ and $Y$ stand for the complex coordinates $z$ and $\bar z$, and consider $Q(X,Y)=X^m(a+bXY)+Y^m(\bar a+\bar bXY)$, which is $X^mA(XY)+Y^m\overline A(XY)$ with $A(s)=a+bs$ as in equation (5). For $\alpha\in\mathbb C$ let $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$ be the polynomial of equation (6).
--
--   Then there exist $c\in\mathbb C$ with $c\ne0$, $\alpha\in\mathbb C$ with $|\alpha|=1$ and $\alpha\notin\mathbb R$, and a real number $k>0$ such that
--   $$Q(cX,\bar cY)=k\,P_\alpha(X,Y)\qquad\text{in }\mathbb C[X,Y].$$
--   The left side is the pullback of $Q$ under the dilation $z\mapsto cz$, which acts on the coordinates by $X\mapsto cX$, $Y\mapsto\bar cY$.
--
--   This is the normalization step in the equality case of Theorem 1. There, for $d\ge5$, the complexified equation of a curve attaining the rotation bound $2d-4$ has the form (5) with $A(s)=a+bs$, $a,b\ne0$ and $a/b\notin\mathbb R$; a substitution $z=cw$ and a rescaling by a positive real constant turn it into $P_\alpha$, the complexified equation of the curve $C_{m,\alpha}$ in (1).
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Theorem 1, equality case, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/Normalization.lean (C. Perassi)

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

theorem CurveSymmetry.normalize_twoParameter {m : ℕ} (hm : 0 < m) {a b : ℂ}
    (hb : b ≠ 0) (hreal : a / b ≠ star (a / b)) :
    ∃ c α : ℂ, ∃ k : ℝ, c ≠ 0 ∧ ‖α‖ = 1 ∧ α ≠ star α ∧ 0 < k ∧
      dilate c (twoParameter m a b) = C (k : ℂ) * familyPolynomial m α := by sorry
