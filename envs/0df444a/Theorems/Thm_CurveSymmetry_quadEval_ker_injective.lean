-- Prove2me | Theorems.Thm_CurveSymmetry_quadEval_ker_injective
-- name    : CurveSymmetry.quadEval_ker_injective
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:50.819752+00:00
-- url     : https://prove2.me/theorems/19d00fb3-daa9-4ab4-8e94-12571d5a1130
-- title:
--   Distinct points of $w^2=h(t)$ have distinct evaluation kernels in $\mathbb C[t][W]/(W^2-h)$
-- statement:
--   Let $h\in\mathbb C[t]$ be any polynomial, let $R_h=\mathbb C[t][W]/(W^2-h(t))$, and for $c,d\in\mathbb C$ with $d^2=h(c)$ let $\operatorname{ev}_{c,d}\colon R_h\to\mathbb C$ be the evaluation $p(t)+q(t)\,W\mapsto p(c)+q(c)\,d$. Let $c,d,c',d'\in\mathbb C$ satisfy $d^2=h(c)$ and $d'^2=h(c')$. Then
--
--   $$
--   \ker\operatorname{ev}_{c,d}=\ker\operatorname{ev}_{c',d'}\ \Longrightarrow\ c=c'\ \text{and}\ d=d'.
--   $$
--
--   Together with the description of the maximal ideals of $R_h$ as evaluation kernels, this gives a bijection between the points of $w^2=h(t)$ and the maximal ideals of $R_h$. It is used to show that distinct points give distinct places of the function field of the double cover (7), for Lemma 4 and Remark 5.
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

theorem CurveSymmetry.quadEval_ker_injective {c d c' d' : ℂ} (hd : d ^ 2 = h.eval c) (hd' : d' ^ 2 = h.eval c')
    (he : RingHom.ker (quadEval h c d hd) = RingHom.ker (quadEval h c' d' hd')) :
    c = c' ∧ d = d' := by sorry
