-- Prove2me | Theorems.Thm_CurveSymmetry_quad_points_over
-- name    : CurveSymmetry.quad_points_over
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:55.637313+00:00
-- url     : https://prove2.me/theorems/c25471e3-7fdb-45ce-860a-84ed2b831e30
-- title:
--   Points of $w^2=h(t)$ over $t=c$: two when $h(c)\ne0$, only $w=0$ when $h(c)=0$
-- statement:
--   Let $h\in\mathbb C[t]$ be any polynomial and $c\in\mathbb C$. The solutions $d$ of $d^2=h(c)$, that is, the points $(c,d)$ of the affine curve $w^2=h(t)$ over $t=c$, are as follows:
--
--   1. if $h(c)\ne0$, there is $d_0\in\mathbb C$ with $d_0\ne-d_0$ such that for every $d\in\mathbb C$, $d^2=h(c)$ holds if and only if $d=d_0$ or $d=-d_0$;
--   2. if $h(c)=0$, then for every $d\in\mathbb C$, $d^2=h(c)$ holds if and only if $d=0$.
--
--   In short,
--
--   $$
--   \{d\in\mathbb C:\ d^2=h(c)\}=\begin{cases}\{d_0,-d_0\}\ \text{with}\ d_0\ne-d_0, & h(c)\ne0,\\ \{0\}, & h(c)=0.\end{cases}
--   $$
--
--   This is the fibre count of the double cover over the finite $t$-line: two points over $c$ when $h(c)\ne0$, one when $h(c)=0$. It feeds the count of branch points of the double cover (7) in the proof of Lemma 4.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 4, equation (7), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/QuadraticPlaces.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
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
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (h : ℂ[X])

theorem CurveSymmetry.quad_points_over (c : ℂ) :
    (h.eval c ≠ 0 → ∃ d₀ : ℂ, d₀ ≠ -d₀ ∧ ∀ d : ℂ, d ^ 2 = h.eval c ↔ d = d₀ ∨ d = -d₀) ∧
      (h.eval c = 0 → ∀ d : ℂ, d ^ 2 = h.eval c ↔ d = 0) := by sorry
