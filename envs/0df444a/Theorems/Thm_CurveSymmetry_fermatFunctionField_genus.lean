-- Prove2me | Theorems.Thm_CurveSymmetry_fermatFunctionField_genus
-- name    : CurveSymmetry.fermatFunctionField_genus
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:42:43.316841+00:00
-- url     : https://prove2.me/theorems/b0dbb999-9ed7-4efe-80fc-2a7f46258943
-- title:
--   The function field of $X^4+Y^4=2$, the complexification of $\operatorname{Re}(z^4)=1$, has genus three
-- statement:
--   Let $K_4=\operatorname{Frac}\bigl(\mathbb C[X,Y]/(X^4+Y^4-2)\bigr)$ be the function field of the complex affine curve $X^4+Y^4=2$. In the coordinates $X=z$, $Y=\bar z$ the real curve $\operatorname{Re}(z^4)=1$ reads $X^4+Y^4=2$, so $K_4$ is the function field of its complexification.
--
--   For a field $L\supseteq\mathbb C$, a *place* of $L$ is a valuation ring $\mathcal O$ of $L$ with $\mathbb C\subseteq\mathcal O\ne L$. A Kähler differential $\omega\in\Omega_{L/\mathbb C}$ is *regular* at $\mathcal O$ if it is a $\mathbb C$-linear combination of differentials $u\,dv$ with $u,v\in\mathcal O$, and *holomorphic* if it is regular at every place. The *genus* $g(L)$ is the dimension over $\mathbb C$ of the space of holomorphic differentials of $L$.
--
--   Then
--   $$g(K_4)=3.$$
--
--   This is the genus three in Remark 5 of the note: the normalization of the complexified curve $\operatorname{Re}(z^4)=1$, read as its function field, has genus three, while the curves of the $m=2$ family have genus two.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FermatGenus.lean (C. Perassi)

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

theorem CurveSymmetry.fermatFunctionField_genus : genus (FermatFunctionField 4) = 3 := by sorry
