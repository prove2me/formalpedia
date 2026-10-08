-- Prove2me | Theorems.Thm_CurveSymmetry_family_place_classification
-- name    : CurveSymmetry.family_place_classification
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:42.198603+00:00
-- url     : https://prove2.me/theorems/6ac03371-ac9e-495c-afeb-6db14a1b7b07
-- title:
--   Places of $\mathbb C(t)[W]/(W^2-h_\alpha)$ over $\mathbb C$: the points of $w^2=h_\alpha(t)$ and the place at infinity
-- statement:
--   Let $m\ge 1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$ (that is, $\alpha$ is not real), and let $h_\alpha(t)=-t\,(t^m+1)\,(\alpha t^m+\bar\alpha)\in\mathbb C[t]$. Let $L_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha(t))$, with $w$ the class of $W$. In the coordinate $s=1/t$ the double cover becomes the one with parameter $\bar\alpha$: let $L_{\bar\alpha}=\mathbb C(s)[W']/(W'^2-h_{\bar\alpha}(s))$, with $w'$ the class of $W'$, and let $\psi\colon L_\alpha\to L_{\bar\alpha}$ be the ring homomorphism with $\psi(r(t))=r(1/s)$ for $r\in\mathbb C(t)$ and $\psi(w)=w'/s^{m+1}$. Let $\mathcal O'_{0,0}\subseteq L_{\bar\alpha}$ be the local ring of the point $(s,w')=(0,0)$ of $w'^2=h_{\bar\alpha}(s)$, that is, the localization of $\mathbb C[s][W']/(W'^2-h_{\bar\alpha}(s))$ at the kernel of the evaluation $s\mapsto0$, $W'\mapsto0$. The place at infinity of $L_\alpha$ is $\mathcal O_\infty=\psi^{-1}(\mathcal O'_{0,0})$. Finally, for $c,d\in\mathbb C$ with $d^2=h_\alpha(c)$, let $\mathcal O_{c,d}\subseteq L_\alpha$ be the local ring of the point $(c,d)$ of $w^2=h_\alpha(t)$, the localization of $\mathbb C[t][W]/(W^2-h_\alpha(t))$ at the kernel of the evaluation $t\mapsto c$, $W\mapsto d$. Then:
--
--   1. $\mathcal O_\infty\ne L_\alpha$, $\mathcal O_\infty$ contains $\mathbb C$, and $t\notin\mathcal O_\infty$;
--   2. every valuation subring $\mathcal O$ of $L_\alpha$ with $\mathcal O\ne L_\alpha$ that contains $\mathbb C$ is either $\mathcal O_{c,d}$ for some $c,d\in\mathbb C$ with $d^2=h_\alpha(c)$, or $\mathcal O_\infty$.
--
--   Thus every place of $L_\alpha$ containing the constants lies in the list
--
--   $$
--   \{\mathcal O_{c,d}:\ c,d\in\mathbb C,\ d^2=h_\alpha(c)\}\ \cup\ \{\mathcal O_\infty\}.
--   $$
--
--   This is the complete list of places of the function field of $V_\alpha$, in the form of the double cover (7) from the proof of Lemma 4: the points of the affine curve $w^2=h_\alpha(t)$ and one place over $t=\infty$. The genus in Lemma 4 is defined through differentials that are regular at every place, so this list is what that computation ranges over; it also serves Remark 5.
--
--   **Formalization Note**: $m>0$ and $\alpha\ne\bar\alpha$ are `Fact` instances; a place is a valuation subring different from the whole field.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 4, equation (7), p. 3; Lemma 4, pp. 3-4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/QuadraticInfinity.lean (C. Perassi)

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

theorem CurveSymmetry.family_place_classification :
    (familyInfinityPlace m α ≠ ⊤ ∧
        (∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ familyInfinityPlace m α) ∧
        algebraMap ℂ[X] (QuadField (familyH m α)) X ∉ familyInfinityPlace m α) ∧
      ∀ O : ValuationSubring (QuadField (familyH m α)), O ≠ ⊤ →
        (∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ O) →
          (∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), O = quadPlace (familyH m α) c d hd) ∨
            O = familyInfinityPlace m α := by sorry
