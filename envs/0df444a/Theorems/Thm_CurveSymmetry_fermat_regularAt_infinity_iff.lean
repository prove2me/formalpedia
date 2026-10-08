-- Prove2me | Theorems.Thm_CurveSymmetry_fermat_regularAt_infinity_iff
-- name    : CurveSymmetry.fermat_regularAt_infinity_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:02.885775+00:00
-- url     : https://prove2.me/theorems/8fbe22a8-aaab-4531-a0b2-94727fdcc975
-- title:
--   Regularity of $F\,dx$ at a place over $x=\infty$ of $x^4+y^4=2$, read in the chart $x=1/s$, $y=r/s$
-- statement:
--   Let $K=\mathbb C(x)[Y]/(Y^4-(2-x^4))$ be the function field of the quartic $x^4+y^4=2$, written as the Kummer cover $y^4=2-x^4$; here $y\in K$ is the class of $Y$, so that $x^4+y^4=2$ in $K$. For the chart at infinity $x=1/s$, $y=r/s$, let $K'=\mathbb C(s)[T]/(T^4-(2s^4-1))$, with $r$ the class of $T$, so that $r^4=2s^4-1$, and let $\varphi\colon K\to K'$ be the ring homomorphism with $\varphi(q(x))=q(1/s)$ for $q\in\mathbb C(x)$ and $\varphi(y)=r/s$. Fix $\zeta\in\mathbb C$ with $\zeta^4=-1$, so that $(0,\zeta)$ is a point of $r^4=2s^4-1$, and let $\mathcal O'\subseteq K'$ be its local ring: the localization of $\mathbb C[s][T]/(T^4-(2s^4-1))$ at the kernel of the evaluation $s\mapsto0$, $T\mapsto\zeta$, viewed inside $K'$. Put $\mathcal P_\infty=\varphi^{-1}(\mathcal O')$, a valuation ring of $K$ (a place of $K$ over $x=\infty$).
--
--   Let $\Omega_{K/\mathbb C}$ be the $K$-module of Kähler differentials of $K$ over $\mathbb C$, with universal derivation $d\colon K\to\Omega_{K/\mathbb C}$. A differential is *regular at* a valuation ring $\mathcal O$ of $K$ if it is a $\mathbb C$-linear combination of differentials $u\,dv$ with $u,v\in\mathcal O$.
--
--   Then for every $F\in K$,
--   $$F\,dx\ \text{is regular at}\ \mathcal P_\infty\iff\frac{\varphi(F)}{s^2}\in\mathcal O'.$$
--
--   This turns regularity at a place of the quartic over $x=\infty$ into membership in an explicit local ring of the chart. It is used to bound the degrees of the coefficients of the holomorphic differentials of the quartic, in the computation of its genus three, which enters Remark 5 of the note.
--
--   **Formalization Note**: $\zeta$ is one fourth root of $-1$, selected by choice, and the statement concerns that root. $\mathcal P_\infty$ is defined as the preimage of the place of $K'$ at $(0,\zeta)$ under the $\mathbb C$-algebra isomorphism $K\to K'$ whose underlying map is $\varphi$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FermatInfinity.lean (C. Perassi)

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

theorem CurveSymmetry.fermat_regularAt_infinity_iff (F : (KummerField 4 fermatQuartic)) :
    F • KaehlerDifferential.D ℂ (KummerField 4 fermatQuartic) quarticX ∈ regularAt fermatInfinityPlace ↔
      fermatInfinityMap F * (dualS⁻¹) ^ 2 ∈ dualLocalRing := by sorry
