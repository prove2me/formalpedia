-- Prove2me | Theorems.Thm_CurveSymmetry_quad_regular_points_coeff
-- name    : CurveSymmetry.quad_regular_points_coeff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:50.288572+00:00
-- url     : https://prove2.me/theorems/350fb343-caac-4b9f-a353-dbe30eb07701
-- title:
--   Regularity of $f\,dt$ at every finite point of $w^2=h(t)$ gives $f\,w=a(t)+b(t)\,w$ with polynomials $a,b$
-- statement:
--   Let $h\in\mathbb C[t]$ be a squarefree polynomial such that $W^2-h(t)$ is irreducible over $\mathbb C(t)$. Let $K_h=\mathbb C(t)[W]/(W^2-h(t))$, with $w$ the class of $W$, so that $w^2=h(t)$, and let $\Omega_{K_h/\mathbb C}$ be its module of Kähler differentials, with universal derivation $d$. For a point $(t_0,w_0)\in\mathbb C^2$ with $w_0^2=h(t_0)$, let $\mathcal O_{(t_0,w_0)}\subset K_h$ be the local ring at $(t_0,w_0)$ of the affine curve $w^2=h(t)$, that is, the localization of $\mathbb C[t][W]/(W^2-h)$ at the maximal ideal of $(t_0,w_0)$, viewed inside $K_h$. A differential $\omega\in\Omega_{K_h/\mathbb C}$ is *regular at* $(t_0,w_0)$ if $f\in\mathcal O_{(t_0,w_0)}$ whenever $u\in\mathcal O_{(t_0,w_0)}$ generates the maximal ideal of $\mathcal O_{(t_0,w_0)}$ and $\omega=f\,du$ with $f\in K_h$.
--
--   Let $f\in K_h$ be such that $f\,dt$ is regular at every point $(t_0,w_0)\in\mathbb C^2$ with $w_0^2=h(t_0)$. Then there are polynomials $a,b\in\mathbb C[t]$ such that
--
--   $$f\,w=a(t)+b(t)\,w .$$
--
--   No condition at infinity is involved. For $h=-t(t^m+1)(\alpha t^m+\bar\alpha)$, the double cover of the family, this is a step towards the description of the holomorphic differentials behind the genus clause of Lemma 4: combined with the condition at the place over $t=\infty$, it shows that every holomorphic $f\,dt$ has $f=a(t)/w$ with $\deg a<m$.
--
--   **Formalization Note**: the squarefreeness of $h$ and the irreducibility of $W^2-h$ over $\mathbb C(t)$ are `Fact` instances.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Lemma 4, pp. 3-4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/HolomorphicSpan.lean (C. Perassi)

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
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]

theorem CurveSymmetry.quad_regular_points_coeff (f : QuadField h)
    (hreg : ∀ (c d : ℂ) (hd : d ^ 2 = h.eval c),
      IsRegularAt h c d hd (f • KaehlerDifferential.D ℂ (QuadField h) (quadT h))) :
    ∃ a b : ℂ[X], f * AdjoinRoot.root (quadRat h) =
      algebraMap ℂ[X] (QuadField h) a +
        algebraMap ℂ[X] (QuadField h) b * AdjoinRoot.root (quadRat h) := by sorry
