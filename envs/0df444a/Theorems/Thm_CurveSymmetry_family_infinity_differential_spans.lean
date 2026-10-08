-- Prove2me | Theorems.Thm_CurveSymmetry_family_infinity_differential_spans
-- name    : CurveSymmetry.family_infinity_differential_spans
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:42:14.430609+00:00
-- url     : https://prove2.me/theorems/bc9b8c0e-457d-4f9b-acf7-c28ee7dc5531
-- title:
--   At the place of $K_\alpha$ over $t=\infty$, a local parameter $x$ with $dx\ne0$ spanning all differentials
-- statement:
--   Let $m\ge1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\overline\alpha$, and put $h_\alpha(t)=-t(t^m+1)(\alpha t^m+\overline\alpha)\in\mathbb C[t]$. Let $K_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha)$ be the function field of the double cover $w^2=h_\alpha(t)$, where $t$ and $w$ denote the classes of $t$ and $W$; in the setting of the note this is the function field of $V_\alpha$, read in the chart of equation (7) with $w=t(t^m+1)Y$. Write $\Omega_{K_\alpha/\mathbb C}$ for the $K_\alpha$-vector space of Kähler differentials of $K_\alpha$ over $\mathbb C$ and $dx$ for the differential of $x\in K_\alpha$.
--
--   For the place over $t=\infty$, put $h_{\overline\alpha}(s)=-s(s^m+1)(\overline\alpha s^m+\alpha)$ and let $K_{\overline\alpha}=\mathbb C(s)[W]/(W^2-h_{\overline\alpha})$ be the function field of the conjugate cover ${w'}^2=h_{\overline\alpha}(s)$, where $s$ and $w'$ denote the classes of $s$ and $W$. Since $h_{\overline\alpha}(0)=0$, the point $(s,w')=(0,0)$ lies on this cover; let $\mathcal O'_{(0,0)}\subset K_{\overline\alpha}$ be the localization of $\mathbb C[s][W]/(W^2-h_{\overline\alpha})$ at the maximal ideal of this point (the kernel of $s\mapsto0$, $w'\mapsto0$), a discrete valuation ring, whose *uniformizers* are the generators of its maximal ideal. Let $\varphi\colon K_\alpha\to K_{\overline\alpha}$ be the isomorphism of $\mathbb C$-algebras with $\varphi(t)=1/s$ and $\varphi(w)=w'\,s^{-(m+1)}$, the chart $s=1/t$, $w'=w\,s^{m+1}$ at infinity. The place of $K_\alpha$ over $t=\infty$ has valuation ring $\mathcal O_\infty=\varphi^{-1}(\mathcal O'_{(0,0)})$.
--
--   There exists $x\in K_\alpha$ such that:
--
--   1. $x\in\mathcal O_\infty$;
--   2. $\varphi(x)=u$ for some uniformizer $u$ of $\mathcal O'_{(0,0)}$;
--   3. $dx$ spans $\Omega_{K_\alpha/\mathbb C}$ over $K_\alpha$,
--      $$\Omega_{K_\alpha/\mathbb C}=K_\alpha\,dx;$$
--   4. $dx\ne0$.
--
--   This carries the description of differentials at point places to the place over $t=\infty$, which the chart $\varphi$ identifies with the point place $(0,0)$ of the conjugate cover. It belongs to the local study of differentials that the formalization carries out for the genus clause of Lemma 4 of the note (the normalization of $V_\alpha$ has genus $m$).
--
--   **Formalization Note**: the hypotheses $m\ge1$ and $\alpha\ne\overline\alpha$ are `Fact` instances; the condition $|\alpha|=1$ of the note is not assumed. The place over $t=\infty$ is defined through the chart: $\mathcal O_\infty$ is the preimage under $\varphi$ of the valuation ring of the point place $(0,0)$ of the conjugate cover.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Lemma 4, pp. 3-4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/InfinityDifferentials.lean (C. Perassi)

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

theorem CurveSymmetry.family_infinity_differential_spans :
    ∃ x : QuadField (familyH m α),
      x ∈ familyInfinityPlace m α ∧
        (∃ u : quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α),
          IsLocalRing.maximalIdeal
              (quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α)) =
            Ideal.span {u} ∧ familyInfinityMap m α x = (u : QuadField (familyH m (star α)))) ∧
        Submodule.span (QuadField (familyH m α))
            {KaehlerDifferential.D ℂ (QuadField (familyH m α)) x} = ⊤ ∧
          KaehlerDifferential.D ℂ (QuadField (familyH m α)) x ≠ 0 := by sorry
