-- Prove2me | Theorems.Thm_CurveSymmetry_anti_support
-- name    : CurveSymmetry.anti_support
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:27.51599+00:00
-- url     : https://prove2.me/theorems/4444284e-bf39-4a5f-8a8e-8d05141a34c4
-- title:
--   Monomials of a polynomial negated by a rotation of order $2m>\deg P$ have weight $\pm m$
-- statement:
--   Let $m\ge 1$ be an integer and let $\zeta\in\mathbb C$ be a primitive $2m$-th root of unity. Let $P=\sum_{a,b\ge 0}p_{ab}X^aY^b\in\mathbb C[X,Y]$ be a polynomial of total degree $\deg P<2m$ that changes sign under the substitution $X\mapsto\zeta X$, $Y\mapsto\zeta^{-1}Y$:
--
--   $$
--   P(\zeta X,\zeta^{-1}Y)=-P(X,Y).
--   $$
--
--   Then every exponent $(a,b)$ with $p_{ab}\ne 0$ satisfies
--
--   $$
--   a=b+m\qquad\text{or}\qquad b=a+m,
--   $$
--
--   that is, every monomial $X^aY^b$ of $P$ has weight $a-b=\pm m$.
--
--   In the coordinates $X=z$, $Y=\bar z$ of the note, the substitution is the pullback of the equation by the rotation $z\mapsto\zeta z$. This is the weight restriction in the proof of Theorem 1 that leads to the radial form (5): when a rotation of order $N=2m$ greater than the degree acts on the equation by the sign $\varepsilon=-1$ of (4), only the weights $m$ and $-m$ can occur. It is used to derive the shape of $P$ in equation (5).
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), proof of Theorem 1, equation (5), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/RotationSupport.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.anti_support {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hdeg : P.totalDegree < 2 * m) (hanti : rotate ζ P = -P)
    {s : Exponent} (hs : s ∈ P.support) : s 0 = s 1 + m ∨ s 1 = s 0 + m := by sorry
