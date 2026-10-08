-- Prove2me | Theorems.Thm_CurveSymmetry_family_finite_place_classification
-- name    : CurveSymmetry.family_finite_place_classification
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:19.711523+00:00
-- url     : https://prove2.me/theorems/8888f31e-4eca-4769-afaf-86f42fcc4a2f
-- title:
--   Places of $\mathbb C(t)[W]/(W^2-h_\alpha)$ containing $\mathbb C[t]$ are the points of $w^2=h_\alpha(t)$, bijectively
-- statement:
--   Let $m\ge 1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$ (that is, $\alpha$ is not real), and let $h_\alpha(t)=-t\,(t^m+1)\,(\alpha t^m+\bar\alpha)\in\mathbb C[t]$. Let $L_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha(t))$ and $R_\alpha=\mathbb C[t][W]/(W^2-h_\alpha(t))$, mapped into $L_\alpha$ by sending $W$ to the class $w$ of $W$. For $c,d\in\mathbb C$ with $d^2=h_\alpha(c)$, let $\mathfrak m_{c,d}\subset R_\alpha$ be the kernel of the evaluation $t\mapsto c$, $W\mapsto d$, and let $\mathcal O_{c,d}=\{a/s:\ a,s\in R_\alpha,\ s\notin\mathfrak m_{c,d}\}\subseteq L_\alpha$ be the local ring of the point $(c,d)$. Then:
--
--   1. for all $c,d$ with $d^2=h_\alpha(c)$, $\mathcal O_{c,d}\ne L_\alpha$ and $\mathcal O_{c,d}$ contains $\mathbb C[t]$;
--   2. every valuation subring $\mathcal O$ of $L_\alpha$ with $\mathcal O\ne L_\alpha$ and $\mathbb C[t]\subseteq\mathcal O$ equals $\mathcal O_{c,d}$ for some $c,d\in\mathbb C$ with $d^2=h_\alpha(c)$;
--   3. if $d^2=h_\alpha(c)$, $d'^2=h_\alpha(c')$ and $\mathcal O_{c,d}=\mathcal O_{c',d'}$, then $c=c'$ and $d=d'$.
--
--   Hence
--
--   $$
--   \{(c,d)\in\mathbb C^2:\ d^2=h_\alpha(c)\}\ \xrightarrow{\ \sim\ }\ \{\mathcal O\subsetneq L_\alpha\ \text{valuation subring}:\ \mathbb C[t]\subseteq\mathcal O\},\qquad (c,d)\mapsto\mathcal O_{c,d}.
--   $$
--
--   $L_\alpha$ is the function field of $V_\alpha$ in the form of the double cover (7) from the proof of Lemma 4; the statement lists its places over the finite $t$-line, one for each point of the affine curve $w^2=h_\alpha(t)$.
--
--   **Formalization Note**: $m>0$ and $\alpha\ne\bar\alpha$ are `Fact` instances, from which the squarefreeness of $h_\alpha$ and the irreducibility of $W^2-h_\alpha(t)$, needed to build $\mathcal O_{c,d}$, are obtained.
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

theorem CurveSymmetry.family_finite_place_classification {m : ℕ} {α : ℂ} [Fact (0 < m)]
    [Fact (α ≠ star α)] :
    (∀ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), quadPlace (familyH m α) c d hd ≠ ⊤ ∧
        ∀ p : ℂ[X], algebraMap ℂ[X] (QuadField (familyH m α)) p ∈
          quadPlace (familyH m α) c d hd) ∧
      (∀ O : ValuationSubring (QuadField (familyH m α)), O ≠ ⊤ →
        (∀ p : ℂ[X], algebraMap ℂ[X] (QuadField (familyH m α)) p ∈ O) →
          ∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), O = quadPlace (familyH m α) c d hd) ∧
      (∀ (c d c' d' : ℂ) (hd : d ^ 2 = (familyH m α).eval c)
        (hd' : d' ^ 2 = (familyH m α).eval c'),
        quadPlace (familyH m α) c d hd = quadPlace (familyH m α) c' d' hd' → c = c' ∧ d = d') := by sorry
