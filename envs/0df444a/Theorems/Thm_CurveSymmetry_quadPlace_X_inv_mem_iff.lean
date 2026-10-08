-- Prove2me | Theorems.Thm_CurveSymmetry_quadPlace_X_inv_mem_iff
-- name    : CurveSymmetry.quadPlace_X_inv_mem_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:45:08.416391+00:00
-- url     : https://prove2.me/theorems/b681d4e4-c518-4786-8907-086370e65c48
-- title:
--   The local ring of $w^2=h(t)$ at a point $(c,d)$ contains $1/t$ if and only if $c\ne0$
-- statement:
--   Let $h\in\mathbb C[t]$ be squarefree and such that $W^2-h(t)$ is irreducible in $\mathbb C(t)[W]$, and let $L_h=\mathbb C(t)[W]/(W^2-h(t))$. For $c,d\in\mathbb C$ with $d^2=h(c)$, let $\mathcal O_{c,d}\subseteq L_h$ be the local ring of the point $(c,d)$ of $w^2=h(t)$: the localization of $\mathbb C[t][W]/(W^2-h(t))$ at the kernel of the evaluation $t\mapsto c$, $W\mapsto d$, viewed inside $L_h$. Then
--
--   $$
--   t^{-1}\in\mathcal O_{c,d}\iff c\ne0.
--   $$
--
--   It is used in the coordinate $s=1/t$, for the double cover rewritten as $w'^2=h_{\bar\alpha}(s)$, to identify the place at infinity of the double cover (7) when its places are classified, for Lemma 4 and Remark 5.
--
--   **Formalization Note**: the two hypotheses on $h$ are `Fact` instances.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 4, equation (7), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/QuadraticInfinity.lean (C. Perassi)

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
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

theorem CurveSymmetry.quadPlace_X_inv_mem_iff (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
    (c d : ℂ) (hd : d ^ 2 = h.eval c) :
    (algebraMap ℂ[X] (QuadField h) X)⁻¹ ∈ quadPlace h c d hd ↔ c ≠ 0 := by sorry
