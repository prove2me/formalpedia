-- Prove2me | Theorems.Thm_CurveSymmetry_fermat_degree
-- name    : CurveSymmetry.fermat_degree
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:42:04.674141+00:00
-- url     : https://prove2.me/theorems/4713e9ab-c08f-4a05-b180-5649fada7ab3
-- title:
--   The polynomial $X^d+Y^d-2$ has total degree $d$
-- statement:
--   Let $d\ge 1$ be an integer and consider $X^d+Y^d-2\in\mathbb C[X,Y]$, whose real locus in the coordinates $X=z$, $Y=\bar z$ is the curve $\operatorname{Re}(z^d)=1$. Its total degree is $d$:
--
--   $$
--   \deg\bigl(X^d+Y^d-2\bigr)=d.
--   $$
--
--   It records the degree of the sharpness examples $\operatorname{Re}(z^d)=1$ in the proof of Theorem 1.
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

theorem CurveSymmetry.fermat_degree {d : ℕ} (hd : 0 < d) : (fermatPolynomial d).totalDegree = d := by sorry
