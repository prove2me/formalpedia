-- Prove2me | Theorems.Thm_CurveSymmetry_fermat_realLocus_infinite
-- name    : CurveSymmetry.fermat_realLocus_infinite
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:47.995985+00:00
-- url     : https://prove2.me/theorems/ae6e64ca-4938-44a7-9b32-770554a317f1
-- title:
--   The real curve $\operatorname{Re}(z^d)=1$ is infinite for every $d\ge1$
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. Let $d\ge 1$ be an integer. Then the real locus of $X^d+Y^d-2\in\mathbb C[X,Y]$,
--
--   $$
--   \{z\in\mathbb C: z^d+\bar z^{\,d}=2\}=\{z\in\mathbb C: \operatorname{Re}(z^d)=1\},
--   $$
--
--   is an infinite set.
--
--   The curves $\operatorname{Re}(z^d)=1$ are the sharpness examples in the proof of Theorem 1, and for $d=4$ the example of Remark 5; this verifies that their real loci are infinite, as the hypotheses of Theorem 1 require.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Theorem 1, sharpness examples, p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/Fermat.lean (C. Perassi)

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
open Polynomial

theorem CurveSymmetry.fermat_realLocus_infinite {d : ℕ} (hd : 0 < d) :
    (realLocus (fermatPolynomial d)).Infinite := by sorry
