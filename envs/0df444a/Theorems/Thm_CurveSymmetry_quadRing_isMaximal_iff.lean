-- Prove2me | Theorems.Thm_CurveSymmetry_quadRing_isMaximal_iff
-- name    : CurveSymmetry.quadRing_isMaximal_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:13.216443+00:00
-- url     : https://prove2.me/theorems/dce73bc7-9614-46e6-9aee-435740a73d78
-- title:
--   Maximal ideals of $\mathbb C[t][W]/(W^2-h)$ are the evaluation kernels at the points $(c,d)$ with $d^2=h(c)$
-- statement:
--   Let $h\in\mathbb C[t]$ be any polynomial and let $R_h=\mathbb C[t][W]/(W^2-h(t))$ be the coordinate ring of the affine curve $w^2=h(t)$. For $c,d\in\mathbb C$ with $d^2=h(c)$, let $\operatorname{ev}_{c,d}\colon R_h\to\mathbb C$ be the evaluation at the point $(c,d)$, that is, the ring homomorphism $p(t)+q(t)\,W\mapsto p(c)+q(c)\,d$. Then for every ideal $\mathfrak m$ of $R_h$,
--
--   $$
--   \mathfrak m\ \text{is maximal}\iff\mathfrak m=\ker\operatorname{ev}_{c,d}\ \text{for some}\ c,d\in\mathbb C\ \text{with}\ d^2=h(c).
--   $$
--
--   So the maximal ideals of $R_h$ are the points of the affine double cover $w^2=h(t)$. This is used to identify the places over the finite $t$-line of the function field of the double cover (7), in the formal treatment of Lemma 4 and Remark 5.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 4, equation (7), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/QuadraticRing.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
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
variable (h : ℂ[X])

theorem CurveSymmetry.quadRing_isMaximal_iff (𝔪 : Ideal (QuadRing h)) :
    𝔪.IsMaximal ↔ ∃ (c d : ℂ) (hd : d ^ 2 = h.eval c), 𝔪 = RingHom.ker (quadEval h c d hd) := by sorry
