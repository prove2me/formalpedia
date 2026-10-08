-- Prove2me | Theorems.Thm_CurveSymmetry_irreducible_radial_form
-- name    : CurveSymmetry.irreducible_radial_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:42:46.688985+00:00
-- url     : https://prove2.me/theorems/fda9bf91-06d0-4673-b005-02d370ff4aa7
-- title:
--   An irreducible polynomial in $XY$ is a nonzero multiple of $XY-r$
-- statement:
--   Let $P=\sum_{a,b\ge 0}p_{ab}X^aY^b\in\mathbb C[X,Y]$ be irreducible in $\mathbb C[X,Y]$ and radial, meaning that $p_{ab}\ne 0$ only when $a=b$, so that $P$ is a polynomial in $XY$. Then there exist $c,r\in\mathbb C$ with $c\ne 0$ such that
--
--   $$
--   P=c\,(XY-r).
--   $$
--
--   In the proof of Theorem 1, when a rotation of order greater than the degree fixes the equation, every exponent has $a=b$ and $P=R(XY)$; this is the step at which irreducibility forces $R$ to be linear.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Theorem 1, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/Irreducibility.lean (C. Perassi)

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

theorem CurveSymmetry.irreducible_radial_form {P : BPoly} (hirr : Irreducible P)
    (hdiag : ∀ s ∈ P.support, s 0 = s 1) :
    ∃ a r : ℂ, a ≠ 0 ∧ P = C a * ((X 0 : BPoly) * X 1 - C r) := by sorry
