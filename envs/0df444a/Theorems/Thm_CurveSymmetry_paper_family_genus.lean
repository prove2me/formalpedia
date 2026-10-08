-- Prove2me | Theorems.Thm_CurveSymmetry_paper_family_genus
-- name    : CurveSymmetry.paper_family_genus
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:15.258153+00:00
-- url     : https://prove2.me/theorems/6d9a4d43-2d22-4460-95ec-0156870d467f
-- title:
--   Lemma 4 (genus clause): the function field of the curve $P_\alpha=0$ has genus $m$
-- statement:
--   Let $m\ge1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$. Let $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)\in\mathbb C[X,Y]$ be the polynomial of equation (6) of the note, the complexification of $2\operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)$ in the coordinates $X=z$, $Y=\bar z$, and let $K_{m,\alpha}=\operatorname{Frac}\bigl(\mathbb C[X,Y]/(P_\alpha)\bigr)$ be the function field of the curve $P_\alpha=0$.
--
--   For a field $L\supseteq\mathbb C$, a *place* of $L$ is a valuation ring $\mathcal O$ of $L$ with $\mathbb C\subseteq\mathcal O\ne L$. A Kähler differential $\omega\in\Omega_{L/\mathbb C}$ is *regular* at $\mathcal O$ if it is a $\mathbb C$-linear combination of differentials $u\,dv$ with $u,v\in\mathcal O$, and *holomorphic* if it is regular at every place. The *genus* $g(L)$ is the dimension over $\mathbb C$ of the space of holomorphic differentials of $L$.
--
--   Then
--   $$g(K_{m,\alpha})=m.$$
--
--   This is the genus clause of Lemma 4 of the note, with the normalization of $V_\alpha$ (the closure of $P_\alpha=0$ in $\mathbb P^1\times\mathbb P^1$) read as its function field $K_{m,\alpha}$. The formal statement assumes only $m\ge1$ and $\alpha\notin\mathbb R$, whereas Lemma 4 takes $m\ge2$ and $|\alpha|=1$; its case $m=2$ gives the genus two in Remark 5.
--
--   **Formalization Note**: $m>0$ and $\alpha\ne\bar\alpha$ are `Fact` instance arguments; they make $\mathbb C[X,Y]/(P_\alpha)$ a domain, so that its fraction field is a field.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Lemma 4, pp. 3-4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/PaperRemarks.lean (C. Perassi)

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

theorem CurveSymmetry.paper_family_genus {m : ℕ} [Fact (0 < m)] {α : ℂ} [Fact (α ≠ star α)] :
    genus (FamilyFunctionField m α) = m := by sorry
