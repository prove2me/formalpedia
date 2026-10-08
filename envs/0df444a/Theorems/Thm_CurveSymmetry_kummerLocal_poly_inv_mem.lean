-- Prove2me | Theorems.Thm_CurveSymmetry_kummerLocal_poly_inv_mem
-- name    : CurveSymmetry.kummerLocal_poly_inv_mem
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:08.643364+00:00
-- url     : https://prove2.me/theorems/e4080544-ef26-4483-8215-b38d5d4c989f
-- title:
--   Inverses of polynomials $p(x)$ with $p(x_0)\ne0$ lie in the local ring of $y^n=f(x)$ at $(x_0,y_0)$
-- statement:
--   Let $n\ge1$ be an integer and $f\in\mathbb C[x]$ a squarefree polynomial of degree at least $1$. Let $K=\mathbb C(x)[Y]/(Y^n-f(x))$ be the function field of the Kummer cover $y^n=f(x)$, with $y$ the class of $Y$. Fix a point $(x_0,y_0)\in\mathbb C^2$ with $y_0^n=f(x_0)$, and let $\mathcal O_{(x_0,y_0)}\subset K$ be the local ring at $(x_0,y_0)$ of the affine curve $y^n=f(x)$, that is, the localization of $\mathbb C[x][Y]/(Y^n-f)$ at the maximal ideal of $(x_0,y_0)$, viewed inside $K$.
--
--   Then, for every polynomial $p\in\mathbb C[x]$ with $p(x_0)\ne0$,
--
--   $$p(x)^{-1}\in\mathcal O_{(x_0,y_0)}.$$
--
--   This local fact about Kummer covers is used in the regularity criterion for differentials $F\,dx$ at the points where $f$ vanishes, and in the degree bound at the place over $x=\infty$, in the computation of the genus three of the quartic $y^4=2-x^4$, which is the curve $\operatorname{Re}(z^4)=1$ of Remark 5.
--
--   **Formalization Note**: $n\ne0$ is a `NeZero` instance, and the squarefreeness of $f$ and $\deg f>0$ are `Fact` instances.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/KummerPlaces.lean (C. Perassi)

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
variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]
variable (a b : ℂ) (hb : b ^ n = f.eval a)

theorem CurveSymmetry.kummerLocal_poly_inv_mem (p : ℂ[X]) (hp : p.eval a ≠ 0) :
    (algebraMap ℂ[X] (KummerField n f) p)⁻¹ ∈ kummerLocalRing a b hb := by sorry
