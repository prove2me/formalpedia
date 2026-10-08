-- Prove2me | Theorems.Thm_CurveSymmetry_not_irreducible_pure_powers
-- name    : CurveSymmetry.not_irreducible_pure_powers
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:40.620261+00:00
-- url     : https://prove2.me/theorems/c53cd7b9-020c-44ef-b2c8-e10e932983db
-- title:
--   A binary form $aX^m+bY^m$ with $m\ge2$ is not irreducible over $\mathbb C$
-- statement:
--   Let $m\ge 2$ be an integer and let $a,b\in\mathbb C$ be arbitrary (either may vanish). Then
--
--   $$
--   aX^m+bY^m \text{ is not irreducible in } \mathbb C[X,Y].
--   $$
--
--   In the proof of Theorem 1 this excludes the case of a constant $A$ in the radial form (5): the equation would then be a homogeneous binary form of degree $m\ge 2$, which cannot be irreducible.
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

theorem CurveSymmetry.not_irreducible_pure_powers (m : ℕ) (hm : 2 ≤ m) (a b : ℂ) :
    ¬ Irreducible (C a * (X 0 : BPoly) ^ m + C b * X 1 ^ m) := by sorry
