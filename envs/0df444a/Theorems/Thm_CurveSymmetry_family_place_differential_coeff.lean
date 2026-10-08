-- Prove2me | Theorems.Thm_CurveSymmetry_family_place_differential_coeff
-- name    : CurveSymmetry.family_place_differential_coeff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:01.016059+00:00
-- url     : https://prove2.me/theorems/30853cdd-0d36-45b7-af62-81f4a4a084c8
-- title:
--   At a point place of $w^2=h_\alpha(t)$, every differential of $K_\alpha$ is $f\,du$ for some uniformizer $u$
-- statement:
--   Let $m\ge1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\overline\alpha$, and put $h_\alpha(t)=-t(t^m+1)(\alpha t^m+\overline\alpha)\in\mathbb C[t]$. Let $K_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha)$ be the function field of the double cover $w^2=h_\alpha(t)$, where $t$ and $w$ denote the classes of $t$ and $W$; in the setting of the note this is the function field of $V_\alpha$, read in the chart of equation (7) with $w=t(t^m+1)Y$. Let $A_\alpha=\mathbb C[t][W]/(W^2-h_\alpha)$ be its coordinate ring, viewed inside $K_\alpha$. For a point $(c,d)\in\mathbb C^2$ of the cover, $d^2=h_\alpha(c)$, let $\mathfrak m_{(c,d)}\subset A_\alpha$ be the kernel of the evaluation $t\mapsto c$, $w\mapsto d$, and let $\mathcal O_{(c,d)}=(A_\alpha)_{\mathfrak m_{(c,d)}}\subset K_\alpha$ be the local ring at $(c,d)$, the valuation ring of the point place $(c,d)$ of $K_\alpha$; it is a discrete valuation ring with maximal ideal $\mathfrak m_{(c,d)}\mathcal O_{(c,d)}$. A *uniformizer* is an element of $\mathcal O_{(c,d)}$ generating this maximal ideal. Write $\Omega_{K_\alpha/\mathbb C}$ for the $K_\alpha$-vector space of Kähler differentials of $K_\alpha$ over $\mathbb C$ and $dx$ for the differential of $x\in K_\alpha$.
--
--   Let $(c,d)\in\mathbb C^2$ with $d^2=h_\alpha(c)$ and let $\omega\in\Omega_{K_\alpha/\mathbb C}$. Then there exist a uniformizer $u$ of $\mathcal O_{(c,d)}$ and an element $f\in K_\alpha$ such that
--   $$\omega=f\,du\quad\text{in }\Omega_{K_\alpha/\mathbb C},$$
--   where $du$ is the differential of $u$ regarded as an element of $K_\alpha$.
--
--   Thus every differential has a coefficient against a uniformizer at each point place; regularity of a differential at a place asks that such coefficients lie in the local ring. It belongs to the local study of differentials that the formalization carries out for the genus clause of Lemma 4 of the note (the normalization of $V_\alpha$ has genus $m$).
--
--   **Formalization Note**: the hypotheses $m\ge1$ and $\alpha\ne\overline\alpha$ are `Fact` instances; the condition $|\alpha|=1$ of the note is not assumed.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Lemma 4, pp. 3-4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/PlaceDifferentials.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
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

theorem CurveSymmetry.family_place_differential_coeff (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c)
    (ω : Ω[QuadField (familyH m α)⁄ℂ]) :
    ∃ u : quadLocalRing (familyH m α) c d hd,
      IsLocalRing.maximalIdeal (quadLocalRing (familyH m α) c d hd) = Ideal.span {u} ∧
        ∃ f : QuadField (familyH m α),
          ω = f • KaehlerDifferential.D ℂ (QuadField (familyH m α))
            (u : QuadField (familyH m α)) := by sorry
