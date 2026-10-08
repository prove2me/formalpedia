-- Prove2me | Theorems.Thm_CurveSymmetry_kummer_D_root
-- name    : CurveSymmetry.kummer_D_root
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:54.130676+00:00
-- url     : https://prove2.me/theorems/f6fdff4b-49b8-439f-a426-576e368de0e7
-- title:
--   Differentiating $y^n=f(x)$: $n\,y^{n-1}\,dy=f'(x)\,dx$ in the function field of a Kummer cover
-- statement:
--   Let $n$ be a natural number and $f\in\mathbb C[x]$ a polynomial such that $Y^n-f(x)$ is irreducible over $\mathbb C(x)$. Let $K=\mathbb C(x)[Y]/(Y^n-f(x))$ be the function field of the Kummer cover $y^n=f(x)$ of the $x$-line, with $y$ the class of $Y$, so that $y^n=f(x)$. Let $\Omega_{K/\mathbb C}$ be its module of Kähler differentials, with universal derivation $d$, and let $f'$ be the derivative of $f$.
--
--   Then, in $\Omega_{K/\mathbb C}$,
--
--   $$n\,y^{\,n-1}\,dy=f'(x)\,dx,$$
--
--   where the integer $n$ is viewed as an element of $K$.
--
--   In the check of Remark 5 the quartic $X^4+Y^4=2$, which is $\operatorname{Re}(z^4)=1$ in the coordinates $X=z$, $Y=\bar z$, is treated as the Kummer cover $y^4=2-x^4$. This relation is used to test the regularity of differentials $F\,dx$ at the points where $f$ vanishes, in the computation of the genus three of that quartic.
--
--   **Formalization Note**: the irreducibility of $Y^n-f$ over $\mathbb C(x)$ is a `Fact` instance; it forces $n\ge1$, so the exponent $n-1$ (truncated subtraction in Lean) has its usual meaning.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/KummerField.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_08_Differentials
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
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (n : ℕ) (f : ℂ[X]) [Fact (Irreducible (kummerRat n f))]

theorem CurveSymmetry.kummer_D_root :
    ((n : KummerField n f) * AdjoinRoot.root (kummerRat n f) ^ (n - 1)) •
        KaehlerDifferential.D ℂ (KummerField n f) (AdjoinRoot.root (kummerRat n f)) =
      algebraMap ℂ[X] (KummerField n f) f.derivative •
        KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) := by sorry
