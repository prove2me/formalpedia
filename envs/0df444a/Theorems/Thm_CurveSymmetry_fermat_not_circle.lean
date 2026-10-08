-- Prove2me | Theorems.Thm_CurveSymmetry_fermat_not_circle
-- name    : CurveSymmetry.fermat_not_circle
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:42:54.84813+00:00
-- url     : https://prove2.me/theorems/00711e0a-e9c0-447b-b1d3-f5aea5feac26
-- title:
--   The real curve $\operatorname{Re}(z^d)=1$ is not a circle
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $d\ge 1$ be an integer and let $C=\{z\in\mathbb C: z^d+\bar z^{\,d}-2=0\}=\{z\in\mathbb C: \operatorname{Re}(z^d)=1\}$ be the real locus of $X^d+Y^d-2$. Then $C$ is not a circle:
--
--   $$
--   C\ne\{z\in\mathbb C: |z-c|=R\}\qquad\text{for every }c\in\mathbb C\text{ and every real }R>0.
--   $$
--
--   This verifies, for the sharpness examples $\operatorname{Re}(z^d)=1$ in the proof of Theorem 1, the hypothesis that the curve is not a circle.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Theorem 1, sharpness examples, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/Sharpness.lean (C. Perassi)

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

theorem CurveSymmetry.fermat_not_circle {d : ℕ} (hd : 0 < d) : NotCircle (fermatPolynomial d) := by sorry
