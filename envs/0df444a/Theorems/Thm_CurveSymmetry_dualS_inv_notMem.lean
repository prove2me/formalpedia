-- Prove2me | Theorems.Thm_CurveSymmetry_dualS_inv_notMem
-- name    : CurveSymmetry.dualS_inv_notMem
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:46.224199+00:00
-- url     : https://prove2.me/theorems/8978d5fc-ce71-46f0-bceb-af070c0247ca
-- title:
--   In the chart $r^4=2s^4-1$ at infinity of $x^4+y^4=2$, $1/s$ is not in the local ring at $(0,\zeta)$
-- statement:
--   In the chart $x=1/s$, $y=r/s$ the quartic $x^4+y^4=2$ becomes $r^4=2s^4-1$. Let $R'=\mathbb C[s][T]/(T^4-(2s^4-1))$ and $K'=\mathbb C(s)[T]/(T^4-(2s^4-1))$ be the affine coordinate ring and the function field of this chart, with $r$ the class of $T$. Fix $\zeta\in\mathbb C$ with $\zeta^4=-1$, so that $(0,\zeta)$ is a point of $r^4=2s^4-1$, and let $\mathcal O'\subseteq K'$ be the local ring there: the localization of $R'$ at the kernel of the evaluation $s\mapsto0$, $T\mapsto\zeta$, viewed inside $K'$.
--
--   Then the inverse of the coordinate $s$ does not lie in this local ring:
--   $$s^{-1}\notin\mathcal O'.$$
--   Since $s$ itself lies in $\mathcal O'$, this says that $s$ is not a unit of $\mathcal O'$.
--
--   It is used to show that the corresponding place of the function field of the quartic, where $x$ corresponds to $1/s$, lies over $x=\infty$, and in the degree bound for holomorphic differentials at that place; both are steps of the computation of the genus three in Remark 5 of the note.
--
--   **Formalization Note**: $\zeta$ is one fourth root of $-1$, selected by choice, and the statement concerns that root.
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

theorem CurveSymmetry.dualS_inv_notMem : dualS⁻¹ ∉ dualLocalRing := by sorry
