-- Prove2me | Theorems.Thm_CurveSymmetry_quartic_holomorphic_split
-- name    : CurveSymmetry.quartic_holomorphic_split
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:30.462536+00:00
-- url     : https://prove2.me/theorems/8a5602dd-7439-44cb-8a96-c047b26da3d4
-- title:
--   Holomorphic differentials of $x^4+y^4=2$ split into four holomorphic pieces $a_j(x)\,y^j\,dx/y^3$
-- statement:
--   Let $K=\mathbb C(x)[Y]/(Y^4-(2-x^4))$ be the function field of the quartic $x^4+y^4=2$, written as the Kummer cover $y^4=2-x^4$; here $y\in K$ is the class of $Y$, so that $x^4+y^4=2$ in $K$.
--
--   Let $\Omega_{K/\mathbb C}$ be the $K$-module of Kähler differentials of $K$ over $\mathbb C$, with universal derivation $d\colon K\to\Omega_{K/\mathbb C}$. A differential is *regular at* a valuation ring $\mathcal O$ of $K$ if it is a $\mathbb C$-linear combination of differentials $u\,dv$ with $u,v\in\mathcal O$. A *place* of $K$ is a valuation ring $\mathcal O$ of $K$ with $\mathbb C\subseteq\mathcal O\ne K$. A differential is *holomorphic* if it is regular at every place of $K$; the holomorphic differentials form a $\mathbb C$-subspace $\Omega^{\mathrm{hol}}_K$ of $\Omega_{K/\mathbb C}$.
--
--   Let $\omega\in\Omega^{\mathrm{hol}}_K$. Then there are polynomials $a_0,a_1,a_2,a_3\in\mathbb C[x]$ such that
--   $$\omega=\bigl(a_0(x)+a_1(x)\,y+a_2(x)\,y^2+a_3(x)\,y^3\bigr)\,\frac{dx}{y^3}$$
--   and each of the four differentials $a_0(x)\,dx/y^3$, $a_1(x)\,y\,dx/y^3$, $a_2(x)\,y^2\,dx/y^3$ and $a_3(x)\,y^3\,dx/y^3$ is holomorphic.
--
--   Combined with the degree bound at a place over $x=\infty$, this reduces the holomorphic differentials of the quartic to the span of $dx/y^3$, $x\,dx/y^3$ and $dx/y^2$, a step of the computation of the genus three in Remark 5 of the note.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FermatSplit.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Definitions.Def_CurveSymmetry_10_KummerField
import Definitions.Def_CurveSymmetry_11_KummerLocal
import Definitions.Def_CurveSymmetry_12_FermatGenus
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

theorem CurveSymmetry.quartic_holomorphic_split {ω : Ω[(KummerField 4 fermatQuartic)⁄ℂ]} (hω : ω ∈ holomorphicSpace (KummerField 4 fermatQuartic)) :
    ∃ a₀ a₁ a₂ a₃ : ℂ[X],
      ω = (quarticTerm a₀ 0 + quarticTerm a₁ 1 + quarticTerm a₂ 2 + quarticTerm a₃ 3) •
        KaehlerDifferential.D ℂ (KummerField 4 fermatQuartic) quarticX ∧
      quarticTerm a₀ 0 ∈ quarticHoloCoeffs ∧ quarticTerm a₁ 1 ∈ quarticHoloCoeffs ∧
      quarticTerm a₂ 2 ∈ quarticHoloCoeffs ∧ quarticTerm a₃ 3 ∈ quarticHoloCoeffs := by sorry
