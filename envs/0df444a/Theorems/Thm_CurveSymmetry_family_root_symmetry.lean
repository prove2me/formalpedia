-- Prove2me | Theorems.Thm_CurveSymmetry_family_root_symmetry
-- name    : CurveSymmetry.family_root_symmetry
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:40.919592+00:00
-- url     : https://prove2.me/theorems/0c4d92d3-772e-48aa-8211-9c6c217300aa
-- title:
--   Rotations by $2m$-th roots of unity are symmetries of $C_{m,\alpha}$
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $m\ge 1$ be an integer and let $\alpha\in\mathbb C$ be arbitrary. Let $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$ be the polynomial of equation (6) and $C_{m,\alpha}=\{z\in\mathbb C: P_\alpha(z,\bar z)=0\}$ its real locus, the set where $\operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0$. Let $\zeta\in\mathbb C$ with $\zeta^{2m}=1$. Then the rotation $z\mapsto\zeta z$ is an orientation-preserving Euclidean symmetry of $C_{m,\alpha}$:
--
--   $$
--   |\zeta|=1\qquad\text{and}\qquad \bigl(\zeta z\in C_{m,\alpha}\iff z\in C_{m,\alpha}\bigr) \text{ for all } z\in\mathbb C.
--   $$
--
--   These are the $2m$ rotations $z\mapsto cz$, $c^{2m}=1$, of the group (3) in Theorem 2. They give the lower bound in the count of the orientation-preserving symmetries of $C_{m,\alpha}$, through which the rotation bound of Theorem 1 is attained.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Theorem 1 (p. 1), Theorem 2 (p. 2), Lemma 4 (p. 3), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyRotations.lean (C. Perassi)

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

theorem CurveSymmetry.family_root_symmetry {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hroot : ζ ^ (2 * m) = 1) (α : ℂ) : DirectSymmetry (realLocus (familyPolynomial m α)) ζ 0 := by sorry
