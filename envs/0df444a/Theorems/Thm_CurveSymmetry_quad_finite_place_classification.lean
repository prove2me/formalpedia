-- Prove2me | Theorems.Thm_CurveSymmetry_quad_finite_place_classification
-- name    : CurveSymmetry.quad_finite_place_classification
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:50.580159+00:00
-- url     : https://prove2.me/theorems/59affbd3-031e-4da3-84cb-7289d7a80e38
-- title:
--   Places of $\mathbb C(t)[W]/(W^2-h)$ containing $\mathbb C[t]$ correspond bijectively to the points of $w^2=h(t)$
-- statement:
--   Let $h\in\mathbb C[t]$ be squarefree and such that $W^2-h(t)$ is irreducible in $\mathbb C(t)[W]$. Let $L_h=\mathbb C(t)[W]/(W^2-h(t))$, a quadratic field extension of $\mathbb C(t)$, and let $R_h=\mathbb C[t][W]/(W^2-h(t))$, mapped into $L_h$ by sending $W$ to the class $w$ of $W$. For $c,d\in\mathbb C$ with $d^2=h(c)$, let $\mathfrak m_{c,d}\subset R_h$ be the kernel of the evaluation $t\mapsto c$, $W\mapsto d$, and let $\mathcal O_{c,d}=\{a/s:\ a,s\in R_h,\ s\notin\mathfrak m_{c,d}\}\subseteq L_h$ be the local ring of the point $(c,d)$. Then:
--
--   1. for all $c,d$ with $d^2=h(c)$, $\mathcal O_{c,d}\ne L_h$ and $\mathcal O_{c,d}$ contains $\mathbb C[t]$;
--   2. every valuation subring $\mathcal O$ of $L_h$ with $\mathcal O\ne L_h$ and $\mathbb C[t]\subseteq\mathcal O$ equals $\mathcal O_{c,d}$ for some $c,d\in\mathbb C$ with $d^2=h(c)$;
--   3. if $d^2=h(c)$, $d'^2=h(c')$ and $\mathcal O_{c,d}=\mathcal O_{c',d'}$, then $c=c'$ and $d=d'$.
--
--   Hence the points of $w^2=h(t)$ correspond bijectively to the places of $L_h$ containing $\mathbb C[t]$:
--
--   $$
--   \{(c,d)\in\mathbb C^2:\ d^2=h(c)\}\ \xrightarrow{\ \sim\ }\ \{\mathcal O\subsetneq L_h\ \text{valuation subring}:\ \mathbb C[t]\subseteq\mathcal O\},\qquad (c,d)\mapsto\mathcal O_{c,d}.
--   $$
--
--   These are the places of the double cover over the finite $t$-line. With $h$ the branch polynomial of the double cover (7), this is used for the genus in Lemma 4 and for Remark 5.
--
--   **Formalization Note**: the two hypotheses on $h$ are `Fact` instances; they make $R_h$ a Dedekind domain with fraction field $L_h$, and $\mathcal O_{c,d}$ is built as the localization of $R_h$ at $\mathfrak m_{c,d}$.
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
variable [hsq : Fact (Squarefree h)] [hirr : Fact (Irreducible (quadRat h))]

theorem CurveSymmetry.quad_finite_place_classification :
    (∀ (c d : ℂ) (hd : d ^ 2 = h.eval c), quadPlace h c d hd ≠ ⊤ ∧
        ∀ p : ℂ[X], algebraMap ℂ[X] (QuadField h) p ∈ quadPlace h c d hd) ∧
      (∀ O : ValuationSubring (QuadField h), O ≠ ⊤ →
        (∀ p : ℂ[X], algebraMap ℂ[X] (QuadField h) p ∈ O) →
          ∃ (c d : ℂ) (hd : d ^ 2 = h.eval c), O = quadPlace h c d hd) ∧
      (∀ (c d c' d' : ℂ) (hd : d ^ 2 = h.eval c) (hd' : d' ^ 2 = h.eval c'),
        quadPlace h c d hd = quadPlace h c' d' hd' → c = c' ∧ d = d') := by sorry
