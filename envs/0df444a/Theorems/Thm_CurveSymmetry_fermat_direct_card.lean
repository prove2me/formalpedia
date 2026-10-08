-- Prove2me | Theorems.Thm_CurveSymmetry_fermat_direct_card
-- name    : CurveSymmetry.fermat_direct_card
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:42:07.839437+00:00
-- url     : https://prove2.me/theorems/855470e2-ad9d-4939-90ff-cd3800188ecb
-- title:
--   For $d\ge2$ the curve $\operatorname{Re}(z^d)=1$ has exactly $d$ orientation-preserving symmetries
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $d\ge 2$ be an integer and let $C=\{z\in\mathbb C: \operatorname{Re}(z^d)=1\}$ be the real locus of $X^d+Y^d-2$. Let $\mathrm{Sym}^+(C)$ be the set of orientation-preserving isometries $T(z)=az+b$ ($a,b\in\mathbb C$, $|a|=1$) such that $T(z)\in C\iff z\in C$ for all $z\in\mathbb C$. Then
--
--   $$
--   |\mathrm{Sym}^+(C)|=d.
--   $$
--
--   This is the rotation count of the sharpness examples in the proof of Theorem 1: with their $d$ reflections these curves attain $|\mathrm{Sym}(C)|=2d$, and their $d$ rotations attain the rotation bound $\max\{d,2d-4\}$ for $d\le 4$. For $d=4$ the curve is the example of Remark 5.
--
--   **Formalization Note**: isometries are recorded by their pairs $(a,b)\in\mathbb C\times\mathbb C$, and the cardinality is the natural-number cardinality; since $d>0$, the equality includes the finiteness of $\mathrm{Sym}^+(C)$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Theorem 1, sharpness examples, p. 3; Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/Sharpness.lean (C. Perassi)

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

theorem CurveSymmetry.fermat_direct_card {d : ℕ} (hd : 2 ≤ d) :
    Nat.card (DirectSymmetries (fermatPolynomial d)) = d := by sorry
