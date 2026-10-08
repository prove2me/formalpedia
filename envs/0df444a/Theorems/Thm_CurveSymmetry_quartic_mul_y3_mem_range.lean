-- Prove2me | Theorems.Thm_CurveSymmetry_quartic_mul_y3_mem_range
-- name    : CurveSymmetry.quartic_mul_y3_mem_range
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:32.324797+00:00
-- url     : https://prove2.me/theorems/c397432d-b82f-4070-92f7-58a456752086
-- title:
--   Holomorphic $F\,dx$ on $x^4+y^4=2$: $F\,y^3$ comes from the affine coordinate ring
-- statement:
--   Let $R=\mathbb C[x][Y]/(Y^4-(2-x^4))$ and $K=\mathbb C(x)[Y]/(Y^4-(2-x^4))$ be the affine coordinate ring and the function field of the quartic $x^4+y^4=2$, written as $y^4=2-x^4$; let $y\in K$ be the class of $Y$ and $\iota\colon R\to K$ the $\mathbb C[x]$-algebra map sending the class of $Y$ to $y$.
--
--   Let $\Omega_{K/\mathbb C}$ be the $K$-module of Kähler differentials of $K$ over $\mathbb C$, with universal derivation $d\colon K\to\Omega_{K/\mathbb C}$. A differential is *regular at* a valuation ring $\mathcal O$ of $K$ if it is a $\mathbb C$-linear combination of differentials $u\,dv$ with $u,v\in\mathcal O$. A *place* of $K$ is a valuation ring $\mathcal O$ of $K$ with $\mathbb C\subseteq\mathcal O\ne K$. A differential is *holomorphic* if it is regular at every place of $K$; the holomorphic differentials form a $\mathbb C$-subspace $\Omega^{\mathrm{hol}}_K$ of $\Omega_{K/\mathbb C}$.
--
--   Let $F\in K$ be such that $F\,dx$ is holomorphic. Then $F\,y^3$ comes from the coordinate ring:
--   $$F\,dx\in\Omega^{\mathrm{hol}}_K\ \Longrightarrow\ \exists\,r\in R:\ \iota(r)=F\,y^3.$$
--
--   This is the affine step in the description of the holomorphic differentials of the quartic: it leads to an expression $F\,y^3=a_0(x)+a_1(x)\,y+a_2(x)\,y^2+a_3(x)\,y^3$ with polynomial coefficients. It is a step of the computation of the genus three in Remark 5 of the note.
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

theorem CurveSymmetry.quartic_mul_y3_mem_range {F : (KummerField 4 fermatQuartic)}
    (hF : F • KaehlerDifferential.D ℂ (KummerField 4 fermatQuartic) quarticX ∈ holomorphicSpace (KummerField 4 fermatQuartic)) :
    ∃ r : KummerRing 4 fermatQuartic, kummerRingMap 4 fermatQuartic r = F * quarticY ^ 3 := by sorry
