-- Prove2me | Theorems.Thm_CurveSymmetry_familyInfinity_shift_sq
-- name    : CurveSymmetry.familyInfinity_shift_sq
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:42:11.968608+00:00
-- url     : https://prove2.me/theorems/a5e363fb-ebb9-4ef6-be28-dde8f6954276
-- title:
--   In the function field of the conjugate cover, $s\,k(s)={w'}^2$ for a polynomial $k$ with $k(0)\ne0$
-- statement:
--   Let $m\ge1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\overline\alpha$, put $h_{\overline\alpha}(s)=-s(s^m+1)(\overline\alpha s^m+\alpha)\in\mathbb C[s]$, and let $K_{\overline\alpha}=\mathbb C(s)[W]/(W^2-h_{\overline\alpha})$ be the function field of the conjugate cover ${w'}^2=h_{\overline\alpha}(s)$, where $s$ and $w'$ denote the classes of $s$ and $W$.
--
--   There exists a polynomial $k\in\mathbb C[s]$ with $k(0)\ne0$ such that
--   $$s\,k(s)={w'}^2\quad\text{in }K_{\overline\alpha}.$$
--
--   Since $k(s)$ is then a unit at the point $(0,0)$ of the conjugate cover, where $w'$ is a uniformizer, $s$ is ${w'}^2$ times a unit there. Through the chart $s=1/t$, $w'=w\,s^{m+1}$ this point describes the place over $t=\infty$ of the function field of $w^2=h_\alpha(t)$, $h_\alpha(t)=-t(t^m+1)(\alpha t^m+\overline\alpha)$. The statement is used in the regularity criterion at that place and in checking that the differentials $t^i\,dt/w$, $0\le i<m$, are regular there; in this way it enters the formal proof of the genus clause of Lemma 4 of the note (the normalization of $V_\alpha$ has genus $m$) and, through the case $m=2$, of Remark 5.
--
--   **Formalization Note**: the hypotheses $m\ge1$ and $\alpha\ne\overline\alpha$ are `Fact` instances; the condition $|\alpha|=1$ of the note is not assumed.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Lemma 4, pp. 3-4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/InfinityRegularity.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
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
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

theorem CurveSymmetry.familyInfinity_shift_sq :
    ∃ k : ℂ[X], k.eval 0 ≠ 0 ∧
      quadT (familyH m (star α)) * algebraMap ℂ[X] (QuadField (familyH m (star α))) k =
        AdjoinRoot.root (quadRat (familyH m (star α))) ^ 2 := by sorry
