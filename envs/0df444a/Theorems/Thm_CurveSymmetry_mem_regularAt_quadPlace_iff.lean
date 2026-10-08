-- Prove2me | Theorems.Thm_CurveSymmetry_mem_regularAt_quadPlace_iff
-- name    : CurveSymmetry.mem_regularAt_quadPlace_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:10.523922+00:00
-- url     : https://prove2.me/theorems/cc2bf9f5-18b2-4290-8f51-4a64be09aa04
-- title:
--   At a point of the double cover $w^2=h(t)$, intrinsic regularity agrees with the uniformizer criterion
-- statement:
--   Let $h\in\mathbb C[t]$ be a squarefree polynomial such that $W^2-h(t)$ is irreducible over $\mathbb C(t)$. Let $K_h=\mathbb C(t)[W]/(W^2-h(t))$, with $w$ the class of $W$, so that $w^2=h(t)$, and let $\Omega_{K_h/\mathbb C}$ be its module of Kähler differentials, with universal derivation $d$. Fix a point $(t_0,w_0)\in\mathbb C^2$ with $w_0^2=h(t_0)$, and let $\mathcal O_{(t_0,w_0)}\subset K_h$ be the local ring at $(t_0,w_0)$ of the affine curve $w^2=h(t)$, that is, the localization of $\mathbb C[t][W]/(W^2-h)$ at the maximal ideal of $(t_0,w_0)$, viewed inside $K_h$; let $\mathfrak m_{(t_0,w_0)}$ be its maximal ideal. This ring is a valuation ring of $K_h$, the place of $K_h$ at $(t_0,w_0)$. Write $\operatorname{Reg}(\mathcal O_{(t_0,w_0)})$ for the space of $\mathbb C$-linear combinations of differentials $a\,db$ with $a,b\in\mathcal O_{(t_0,w_0)}$.
--
--   Then, for every $\omega\in\Omega_{K_h/\mathbb C}$,
--
--   $$\omega\in\operatorname{Reg}(\mathcal O_{(t_0,w_0)})\iff\Bigl(f\in\mathcal O_{(t_0,w_0)}\ \text{whenever } u\in\mathcal O_{(t_0,w_0)},\ \mathfrak m_{(t_0,w_0)}=(u),\ f\in K_h\ \text{and}\ \omega=f\,du\Bigr).$$
--
--   The right-hand side is the explicit criterion: the coefficient of $\omega$ against any uniformizer lies in the local ring.
--
--   For the double cover $w^2=-t(t^m+1)(\alpha t^m+\bar\alpha)$ of the family, this is used to identify the intrinsically defined holomorphic differentials with the explicitly computed ones, and hence to obtain the genus of the function field of the curve $P_\alpha=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)=0$: genus $m$ in Lemma 4, genus two for $m=2$ in Remark 5.
--
--   **Formalization Note**: the place is a `ValuationSubring` with the same elements as the local ring, which is a subalgebra of $K_h$. The squarefreeness of $h$ and the irreducibility of $W^2-h$ are `Fact` instances.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyGenus.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Definitions.Def_CurveSymmetry_10_KummerField
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
import Mathlib.LinearAlgebra.Dimension.Finrank
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
  (c d : ℂ) (hd : d ^ 2 = h.eval c)

theorem CurveSymmetry.mem_regularAt_quadPlace_iff (ω : Ω[QuadField h⁄ℂ]) :
    ω ∈ regularAt (quadPlace h c d hd) ↔ IsRegularAt h c d hd ω := by sorry
