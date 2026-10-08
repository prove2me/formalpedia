-- Prove2me | Theorems.Thm_CurveSymmetry_family_ramified_uniformizer
-- name    : CurveSymmetry.family_ramified_uniformizer
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:53.135894+00:00
-- url     : https://prove2.me/theorems/96e209da-f3f5-43e2-88d0-d8c9c4e3c2ed
-- title:
--   Points of $w^2=h_\alpha(t)$ over roots of $h_\alpha$: $w$ is a uniformizer and $h_\alpha'(t)$ is a unit
-- statement:
--   Let $m\ge1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\overline\alpha$, and put $h_\alpha(t)=-t(t^m+1)(\alpha t^m+\overline\alpha)\in\mathbb C[t]$. Let $K_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha)$ be the function field of the double cover $w^2=h_\alpha(t)$, where $t$ and $w$ denote the classes of $t$ and $W$; in the setting of the note this is the function field of $V_\alpha$, read in the chart of equation (7) with $w=t(t^m+1)Y$. Let $A_\alpha=\mathbb C[t][W]/(W^2-h_\alpha)$ be its coordinate ring, viewed inside $K_\alpha$. For a point $(c,d)\in\mathbb C^2$ of the cover, $d^2=h_\alpha(c)$, let $\mathfrak m_{(c,d)}\subset A_\alpha$ be the kernel of the evaluation $t\mapsto c$, $w\mapsto d$, and let $\mathcal O_{(c,d)}=(A_\alpha)_{\mathfrak m_{(c,d)}}\subset K_\alpha$ be the local ring at $(c,d)$, the valuation ring of the point place $(c,d)$ of $K_\alpha$; it is a discrete valuation ring with maximal ideal $\mathfrak m_{(c,d)}\mathcal O_{(c,d)}$. A *uniformizer* is an element of $\mathcal O_{(c,d)}$ generating this maximal ideal.
--
--   Let $c\in\mathbb C$ with $h_\alpha(c)=0$, so that $(c,0)$ is a point of the cover, and let $h_\alpha'$ be the derivative of $h_\alpha$. Then:
--
--   1. the image of $w$ in $\mathcal O_{(c,0)}$ is a uniformizer,
--      $$\mathfrak m_{(c,0)}\mathcal O_{(c,0)}=w\,\mathcal O_{(c,0)};$$
--   2. $h_\alpha'(t)$ is a unit of $\mathcal O_{(c,0)}$.
--
--   This is the ramified case of the local study of differentials on $K_\alpha$ that the formalization carries out for the genus clause of Lemma 4 of the note (the normalization of $V_\alpha$ has genus $m$): with the identity $h_\alpha'(t)\,f\,dt=2fw\,dw$, a differential $f\,dt$ is read against the uniformizer $w$ with coefficient $2fw/h_\alpha'(t)$, the factor $h_\alpha'(t)$ being a unit.
--
--   **Formalization Note**: the hypotheses $m\ge1$ and $\alpha\ne\overline\alpha$ are `Fact` instances; the condition $|\alpha|=1$ of the note is not assumed.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Lemma 4, pp. 3-4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/PlaceUniformizers.lean (C. Perassi)

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

theorem CurveSymmetry.family_ramified_uniformizer (c : ℂ) (hc : (familyH m α).eval c = 0) :
    IsLocalRing.maximalIdeal (quadLocalRing (familyH m α) c 0 (familyH_root_point c hc)) =
        Ideal.span {algebraMap (QuadRing (familyH m α))
          (quadLocalRing (familyH m α) c 0 (familyH_root_point c hc))
          (AdjoinRoot.root (quadPoly (familyH m α)))} ∧
      IsUnit (algebraMap (QuadRing (familyH m α))
        (quadLocalRing (familyH m α) c 0 (familyH_root_point c hc))
        (algebraMap ℂ[X] (QuadRing (familyH m α)) (familyH m α).derivative)) := by sorry
