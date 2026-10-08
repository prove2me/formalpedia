-- Prove2me | Theorems.Thm_CurveSymmetry_isometry_sign_of_realLocus
-- name    : CurveSymmetry.isometry_sign_of_realLocus
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:43.221037+00:00
-- url     : https://prove2.me/theorems/1b1f5be9-6749-4ca7-8fc7-a0bd56edd8f4
-- title:
--   Lemma 3 in complex coordinates: isometries preserving $\{P(z,\bar z)=0\}$ multiply $P(z,\bar z)$ by $\pm1$
-- statement:
--   Let $P\in\mathbb{C}[X,Y]$ be irreducible, of total degree at least $2$, and let
--
--   $$S=\{z\in\mathbb{C} : P(z,\bar z)=0\}$$
--
--   be its real locus, written in the coordinates $X=z$, $Y=\bar z$. Assume $S$ is infinite. Let $T$ be an isometry of the Euclidean plane $\mathbb{C}$ preserving $S$, that is, $T(z)\in S\iff z\in S$ for every $z\in\mathbb{C}$.
--
--   Then there is a sign $\varepsilon\in\{1,-1\}$ such that
--
--   $$P\bigl(T(z),\overline{T(z)}\bigr)=\varepsilon\,P(z,\bar z)\qquad\text{for every } z\in\mathbb{C},$$
--
--   and $\varepsilon=1$ whenever $T$ reverses orientation, that is, whenever there are $a,b\in\mathbb{C}$ with $T(z)=a\bar z+b$ for all $z$.
--
--   This is the sign clause of Lemma 3 of the note in the coordinates $X=z$, $Y=\bar z$ introduced after it, where a real equation $f$ becomes $P(X,Y)=f\bigl((X+Y)/2,(X-Y)/(2i)\bigr)$; Lemma 3 itself, for a real Cartesian equation, is derived from it. The note's standing assumption that the curve is not a circle is not needed.
--
--   **Formalization Note**: $T$ ranges over the subgroup of the isometries `ℂ ≃ᵢ ℂ` preserving $S$, $\varepsilon$ is a complex number equal to $1$ or $-1$, and no condition is imposed on the coefficients of $P$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 3, p. 2; Lemma 3, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/IsometrySign.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
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

theorem CurveSymmetry.isometry_sign_of_realLocus {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite)
    (T : isometrySymmetryGroup P) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      (∀ z : ℂ, eval (fun i : Fin 2 => if i = 0 then T.val z else star (T.val z)) P =
        ε * eval (fun i : Fin 2 => if i = 0 then z else star z) P) ∧
      ((∃ a b : ℂ, ∀ z : ℂ, T.val z = a * star z + b) → ε = 1) := by sorry
