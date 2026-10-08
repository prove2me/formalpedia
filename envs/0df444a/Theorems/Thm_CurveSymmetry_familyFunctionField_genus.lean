-- Prove2me | Theorems.Thm_CurveSymmetry_familyFunctionField_genus
-- name    : CurveSymmetry.familyFunctionField_genus
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:55.88098+00:00
-- url     : https://prove2.me/theorems/e93827dd-14ba-4396-85e1-6c5ab4b6b342
-- title:
--   The function field of $X^m(\alpha+XY)+Y^m(\bar\alpha+XY)=0$ has genus $m$
-- statement:
--   Let $m\ge1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$, and let $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)\in\mathbb C[X,Y]$ be the polynomial of equation (6) of the note. Under these hypotheses $\mathbb C[X,Y]/(P_\alpha)$ is an integral domain; let $F_\alpha=\operatorname{Frac}\bigl(\mathbb C[X,Y]/(P_\alpha)\bigr)$ be its field of fractions, the function field of the curve $P_\alpha=0$.
--
--   For a field $K$ containing $\mathbb C$, let $\Omega_{K/\mathbb C}$ be its module of Kähler differentials, with universal derivation $d$. A *place* of $K$ is a valuation ring $\mathcal O\ne K$ of $K$ (a subring with $\xi\in\mathcal O$ or $\xi^{-1}\in\mathcal O$ for every nonzero $\xi\in K$) that contains $\mathbb C$. A differential is *regular at* $\mathcal O$ if it is a $\mathbb C$-linear combination of differentials $a\,db$ with $a,b\in\mathcal O$. The *holomorphic differentials* $H(K)\subseteq\Omega_{K/\mathbb C}$ are those regular at every place of $K$, and the *genus* of $K$ is $g(K)=\dim_{\mathbb C}H(K)$.
--
--   Then
--
--   $$g(F_\alpha)=m.$$
--
--   This gives the genus clause of Lemma 4, where $V_\alpha$ is the closure of the curve $P_\alpha=0$ in $\mathbb P^1\times\mathbb P^1$, the genus of the normalization of $V_\alpha$ being read as the genus of its function field; it holds for every $m\ge1$ and every nonreal $\alpha$, while the note assumes $|\alpha|=1$. For $m=2$ it is the genus two of the family in Remark 5, compared there with the genus three of $\operatorname{Re}(z^4)=1$.
--
--   **Formalization Note**: the hypotheses $m>0$ and $\alpha\ne\bar\alpha$ are `Fact` instances. The field structure on $F_\alpha$ comes from an instance stating that $\mathbb C[X,Y]/(P_\alpha)$ is a domain, derived in the formalization from the irreducibility of $P_\alpha$. The genus is `Module.finrank` of the holomorphic differentials.
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
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

theorem CurveSymmetry.familyFunctionField_genus : genus (FamilyFunctionField m α) = m := by sorry
