-- Prove2me | Theorems.Thm_CurveSymmetry_quad_ramified_uniformizer
-- name    : CurveSymmetry.quad_ramified_uniformizer
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:18.217739+00:00
-- url     : https://prove2.me/theorems/cfeb5882-7bf4-4f4c-9b48-51d2b4e4a37f
-- title:
--   At a point $(c,d)$ of $w^2=h(t)$ with $h(c)=0$, $w$ is a uniformizer of the local ring
-- statement:
--   Let $h\in\mathbb C[t]$ be a squarefree polynomial such that $W^2-h$ is irreducible in $\mathbb C(t)[W]$. Let $K=\mathbb C(t)[W]/(W^2-h)$ be the function field of the double cover $w^2=h(t)$, where $t$ and $w$ denote the classes of $t$ and $W$, and let $A=\mathbb C[t][W]/(W^2-h)$ be its coordinate ring, viewed inside $K$. For a point $(c,d)\in\mathbb C^2$ of the cover, $d^2=h(c)$, let $\mathfrak m_{(c,d)}\subset A$ be the kernel of the evaluation $A\to\mathbb C$, $t\mapsto c$, $w\mapsto d$, and let $\mathcal O_{(c,d)}=A_{\mathfrak m_{(c,d)}}\subset K$ be the local ring at $(c,d)$, the valuation ring of the point place $(c,d)$ of $K$; it is a discrete valuation ring with maximal ideal $\mathfrak m_{(c,d)}\mathcal O_{(c,d)}$. A *uniformizer* is an element of $\mathcal O_{(c,d)}$ generating this maximal ideal.
--
--   Let $(c,d)\in\mathbb C^2$ with $d^2=h(c)$ and $h(c)=0$ (so $d=0$). Then the image of $w\in A$ in $\mathcal O_{(c,d)}$ generates the maximal ideal:
--   $$\mathfrak m_{(c,d)}\mathcal O_{(c,d)}=w\,\mathcal O_{(c,d)}.$$
--
--   This gives a uniformizer at the ramified point places, those over the roots of $h$. It is used for the regularity criterion of $f\,dt$ at these places and, at the point $(0,0)$ of the conjugate cover through which the family is read near $t=\infty$, for the criterion at the place over $t=\infty$; in this way it enters the formal proof of the genus clause of Lemma 4 of the note (the normalization of $V_\alpha$ has genus $m$) and, through the case $m=2$, of Remark 5.
--
--   **Formalization Note**: the hypotheses that $h$ is squarefree and that $W^2-h$ is irreducible are `Fact` instances, and $d^2=h(c)$ is an explicit hypothesis. $\mathcal O_{(c,d)}$ is a subalgebra of $K$: the localization of $A$ at the kernel of the evaluation map.
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
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)

theorem CurveSymmetry.quad_ramified_uniformizer (hc : h.eval c = 0) :
    IsLocalRing.maximalIdeal (quadLocalRing h c d hd) =
      Ideal.span {algebraMap (QuadRing h) (quadLocalRing h c d hd)
        (AdjoinRoot.root (quadPoly h))} := by sorry
