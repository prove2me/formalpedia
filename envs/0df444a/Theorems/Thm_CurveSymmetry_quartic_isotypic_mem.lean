-- Prove2me | Theorems.Thm_CurveSymmetry_quartic_isotypic_mem
-- name    : CurveSymmetry.quartic_isotypic_mem
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:12.269874+00:00
-- url     : https://prove2.me/theorems/2bfbf7ca-f222-44dd-94f3-c666055fe096
-- title:
--   Eigencomponents under $y\mapsto iy$ stay in a stable subspace of the function field of $x^4+y^4=2$
-- statement:
--   Let $K=\mathbb C(x)[Y]/(Y^4-(2-x^4))$ be the function field of the quartic $x^4+y^4=2$, written as the Kummer cover $y^4=2-x^4$; here $y\in K$ is the class of $Y$, so that $x^4+y^4=2$ in $K$. Let $\sigma$ be the automorphism of $K$ that fixes $\mathbb C(x)$ pointwise and sends $y$ to $iy$; it is in particular a $\mathbb C$-algebra automorphism of $K$.
--
--   Let $V\subseteq K$ be a $\mathbb C$-linear subspace with $\sigma(V)\subseteq V$, and let $G_0,G_1,G_2,G_3\in K$ satisfy
--   $$\sigma(G_0)=i\,G_0,\qquad\sigma(G_1)=-G_1,\qquad\sigma(G_2)=-i\,G_2,\qquad\sigma(G_3)=G_3.$$
--   If $G_0+G_1+G_2+G_3\in V$, then $G_0\in V$, $G_1\in V$, $G_2\in V$ and $G_3\in V$.
--
--   In the formalization $V$ is the space of $F\in K$ with $F\,dx$ holomorphic, which is $\sigma$-stable, and the $G_j$ are the pieces $a_j(x)\,y^j/y^3$, on which $\sigma$ acts by $i^{\,j+1}$. The result shows that each piece of a holomorphic differential is holomorphic, a step of the computation of the genus three in Remark 5 of the note.
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

theorem CurveSymmetry.quartic_isotypic_mem {V : Submodule ℂ (KummerField 4 fermatQuartic)} (hV : ∀ G ∈ V, quarticRot G ∈ V)
    {G₀ G₁ G₂ G₃ : (KummerField 4 fermatQuartic)} (h₀ : quarticRot G₀ = quarticI * G₀) (h₁ : quarticRot G₁ = -G₁)
    (h₂ : quarticRot G₂ = -(quarticI * G₂)) (h₃ : quarticRot G₃ = G₃)
    (hF : G₀ + G₁ + G₂ + G₃ ∈ V) : G₀ ∈ V ∧ G₁ ∈ V ∧ G₂ ∈ V ∧ G₃ ∈ V := by sorry
