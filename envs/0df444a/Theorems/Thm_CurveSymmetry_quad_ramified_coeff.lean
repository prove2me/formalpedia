-- Prove2me | Theorems.Thm_CurveSymmetry_quad_ramified_coeff
-- name    : CurveSymmetry.quad_ramified_coeff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:58.020623+00:00
-- url     : https://prove2.me/theorems/fdd59c0e-d93f-4f34-a00a-6295b37f9bde
-- title:
--   The identity $h'(t)\,f\,dt=2fw\,dw$ for differentials of the function field of $w^2=h(t)$
-- statement:
--   Let $h\in\mathbb C[t]$ be a polynomial such that $W^2-h$ is irreducible in $\mathbb C(t)[W]$, and let $K=\mathbb C(t)[W]/(W^2-h)$ be the function field of the double cover $w^2=h(t)$, where $t$ and $w$ denote the classes of $t$ and $W$. Let $h'$ be the derivative of $h$, write $\Omega_{K/\mathbb C}$ for the $K$-vector space of Kähler differentials of $K$ over $\mathbb C$, and $dx$ for the differential of $x\in K$.
--
--   For every $f\in K$,
--   $$h'(t)\cdot(f\,dt)=(2fw)\,dw\quad\text{in }\Omega_{K/\mathbb C}.$$
--
--   At a point $(c,0)$ with $h(c)=0$, where $w$ is a uniformizer and $h'(t)$ is a unit of the local ring, this expresses $f\,dt$ against $w$ with coefficient $2fw/h'(t)$: $dt$ has order one there. It is used for the regularity criterion at these ramified point places and, through the chart at infinity, at the place over $t=\infty$ of the family; in this way it enters the formal proof of the genus clause of Lemma 4 of the note (the normalization of $V_\alpha$ has genus $m$) and, through the case $m=2$, of Remark 5.
--
--   **Formalization Note**: the irreducibility of $W^2-h$ is a `Fact` instance; $h$ is not assumed squarefree here, and no point of the cover enters the statement.
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
omit [Fact (Squarefree h)]

theorem CurveSymmetry.quad_ramified_coeff (f : QuadField h) :
    algebraMap ℂ[X] (QuadField h) h.derivative •
        (f • KaehlerDifferential.D ℂ (QuadField h) (quadT h)) =
      (2 * f * AdjoinRoot.root (quadRat h)) •
        KaehlerDifferential.D ℂ (QuadField h) (AdjoinRoot.root (quadRat h)) := by sorry
