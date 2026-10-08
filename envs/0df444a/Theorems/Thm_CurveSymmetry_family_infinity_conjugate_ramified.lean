-- Prove2me | Theorems.Thm_CurveSymmetry_family_infinity_conjugate_ramified
-- name    : CurveSymmetry.family_infinity_conjugate_ramified
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:42.733086+00:00
-- url     : https://prove2.me/theorems/5f88d9eb-463f-47eb-9f64-057015d3893b
-- title:
--   At $(0,0)$ on the conjugate cover: $w'$ is a uniformizer, $h_{\overline\alpha}'(s)$ is a unit, and $s\,k(s)={w'}^2$
-- statement:
--   Let $m\ge1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\overline\alpha$, and put $h_{\overline\alpha}(s)=-s(s^m+1)(\overline\alpha s^m+\alpha)\in\mathbb C[s]$, with derivative $h_{\overline\alpha}'$. Let $A_{\overline\alpha}=\mathbb C[s][W]/(W^2-h_{\overline\alpha})$ be the coordinate ring of the conjugate cover ${w'}^2=h_{\overline\alpha}(s)$, where $s$ and $w'$ denote the classes of $s$ and $W$, and let $K_{\overline\alpha}$ be its fraction field. The point $(0,0)$ lies on this cover since $h_{\overline\alpha}(0)=0$; let $\mathfrak m'_{(0,0)}\subset A_{\overline\alpha}$ be the kernel of the evaluation $s\mapsto0$, $w'\mapsto0$, and let $\mathcal O'_{(0,0)}\subset K_{\overline\alpha}$ be the localization of $A_{\overline\alpha}$ at it, a discrete valuation ring.
--
--   Then:
--
--   1. $w'$ is a uniformizer of $\mathcal O'_{(0,0)}$:
--      $$\mathfrak m'_{(0,0)}\mathcal O'_{(0,0)}=w'\,\mathcal O'_{(0,0)};$$
--   2. $h_{\overline\alpha}'(s)$ is a unit of $\mathcal O'_{(0,0)}$;
--   3. there is a polynomial $k\in\mathbb C[s]$ with $k(0)\ne0$ such that $s\,k(s)={w'}^2$ in $A_{\overline\alpha}$.
--
--   The chart $s=1/t$, $w'=w\,s^{m+1}$ identifies the place over $t=\infty$ of the function field of $w^2=h_\alpha(t)$, $h_\alpha(t)=-t(t^m+1)(\alpha t^m+\overline\alpha)$, with this point place of the conjugate cover; the statement records that it is a ramified point, where $s$ is ${w'}^2$ times a unit. It belongs to the local study of differentials that the formalization carries out for the genus clause of Lemma 4 of the note (the normalization of $V_\alpha$ has genus $m$).
--
--   **Formalization Note**: the hypotheses $m\ge1$ and $\alpha\ne\overline\alpha$ are `Fact` instances; the condition $|\alpha|=1$ of the note is not assumed.
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

theorem CurveSymmetry.family_infinity_conjugate_ramified :
    IsLocalRing.maximalIdeal (quadLocalRing (familyH m (star α)) 0 0
          (familyH_star_zero_point m α)) =
        Ideal.span {algebraMap (QuadRing (familyH m (star α)))
          (quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α))
          (AdjoinRoot.root (quadPoly (familyH m (star α))))} ∧
      IsUnit (algebraMap (QuadRing (familyH m (star α)))
        (quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α))
        (algebraMap ℂ[X] (QuadRing (familyH m (star α)))
          (familyH m (star α)).derivative)) ∧
      ∃ k : ℂ[X], k.eval 0 ≠ 0 ∧
        quadShift (familyH m (star α)) 0 *
            algebraMap ℂ[X] (QuadRing (familyH m (star α))) k =
          AdjoinRoot.root (quadPoly (familyH m (star α))) ^ 2 := by sorry
