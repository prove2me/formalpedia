-- Prove2me | Theorems.Thm_CurveSymmetry_quartic_smul_dx_mem_holomorphicSpace
-- name    : CurveSymmetry.quartic_smul_dx_mem_holomorphicSpace
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:09.617733+00:00
-- url     : https://prove2.me/theorems/44a557f8-e9f6-4cd5-b3ff-b0121f2f6680
-- title:
--   Three local tests on the coefficient $F$ that make $F\,dx$ holomorphic on the quartic $x^4+y^4=2$
-- statement:
--   Let $K_4=\mathbb C(x)[Y]/(Y^4-(2-x^4))$, with $y$ the class of $Y$, so that $x^4+y^4=2$. This is the function field of the quartic $X^4+Y^4=2$, written as the cover $y^4=2-x^4$ of the $x$-line; in the coordinates $X=z$, $Y=\bar z$ the real locus of that quartic is the curve $\operatorname{Re}(z^4)=1$ of Remark 5. Let $\Omega_{K_4/\mathbb C}$ be the module of Kähler differentials of $K_4$, with universal derivation $d$.
--
--   A *valuation ring* of $K_4$ is a subring $\mathcal O\subseteq K_4$ with $\xi\in\mathcal O$ or $\xi^{-1}\in\mathcal O$ for every nonzero $\xi\in K_4$, and a *place* of $K_4$ is a valuation ring $\mathcal O\ne K_4$ containing $\mathbb C$. A differential is *regular at* $\mathcal O$ if it is a $\mathbb C$-linear combination of differentials $a\,db$ with $a,b\in\mathcal O$, and $H(K_4)\subseteq\Omega_{K_4/\mathbb C}$ is the space of holomorphic differentials, those regular at every place of $K_4$.
--
--   Let $F\in K_4$ satisfy the following three conditions for every valuation ring $\mathcal O$ of $K_4$:
--
--   1. if $x\in\mathcal O$, $y\in\mathcal O$ and $y^{-1}\in\mathcal O$, then $F\in\mathcal O$;
--   2. if $x\in\mathcal O$, $x^{-1}\in\mathcal O$ and $y\in\mathcal O$, then $F\,y^3x^{-3}\in\mathcal O$;
--   3. if $x^{-1}\in\mathcal O$ and $x\,y^{-1}\in\mathcal O$, then $F\,x^2\in\mathcal O$.
--
--   Then $F\,dx$ is holomorphic:
--
--   $$F\,dx\in H(K_4).$$
--
--   This is the criterion through which $dx/y^3$, $x\,dx/y^3$ and $dx/y^2$ are shown to be holomorphic, which gives the curve $\operatorname{Re}(z^4)=1$ of Remark 5 at least three linearly independent holomorphic differentials.
--
--   **Formalization Note**: the three hypotheses quantify over all valuation subrings of $K_4$, not only over its places.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FermatHolomorphic.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
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
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
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

theorem CurveSymmetry.quartic_smul_dx_mem_holomorphicSpace (F : (KummerField 4 fermatQuartic))
    (h1 : ∀ O : ValuationSubring (KummerField 4 fermatQuartic),
      quarticX ∈ O → quarticY ∈ O → quarticY⁻¹ ∈ O → F ∈ O)
    (h2 : ∀ O : ValuationSubring (KummerField 4 fermatQuartic), quarticX ∈ O → quarticX⁻¹ ∈ O → quarticY ∈ O →
      F * quarticY ^ 3 * quarticX⁻¹ ^ 3 ∈ O)
    (h3 : ∀ O : ValuationSubring (KummerField 4 fermatQuartic), quarticX⁻¹ ∈ O → quarticX * quarticY⁻¹ ∈ O →
      F * quarticX ^ 2 ∈ O) :
    F • KaehlerDifferential.D ℂ (KummerField 4 fermatQuartic) quarticX ∈ holomorphicSpace (KummerField 4 fermatQuartic) := by sorry
