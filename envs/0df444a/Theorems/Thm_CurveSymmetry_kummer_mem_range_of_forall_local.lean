-- Prove2me | Theorems.Thm_CurveSymmetry_kummer_mem_range_of_forall_local
-- name    : CurveSymmetry.kummer_mem_range_of_forall_local
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:02.512185+00:00
-- url     : https://prove2.me/theorems/4f2d0e7f-dadc-4a68-a163-a3e98e00f606
-- title:
--   Elements of the Kummer function field lying in every affine local ring come from the coordinate ring
-- statement:
--   Let $n\ge1$ be an integer and let $f\in\mathbb C[x]$ be a squarefree polynomial of positive degree. Let $R=\mathbb C[x][Y]/(Y^n-f)$ be the affine coordinate ring of the Kummer cover $y^n=f(x)$ and $K=\mathbb C(x)[Y]/(Y^n-f)$ its function field (a field, as $Y^n-f$ is irreducible over $\mathbb C(x)$). Write $y\in K$ for the class of $Y$, so that $y^n=f(x)$, and $\iota\colon R\to K$ for the $\mathbb C[x]$-algebra map sending the class of $Y$ to $y$.
--
--   For each point $(a,b)\in\mathbb C^2$ of the cover, that is $b^n=f(a)$, let $\mathrm{ev}_{(a,b)}\colon R\to\mathbb C$ be the evaluation $x\mapsto a$, $Y\mapsto b$, and let $\mathcal O_{(a,b)}\subseteq K$ be the local ring at $(a,b)$: the localization of $R$ at $\ker\mathrm{ev}_{(a,b)}$, viewed inside $K$, that is, the quotients $\iota(p)/\iota(q)$ with $p,q\in R$ and $\mathrm{ev}_{(a,b)}(q)\ne0$.
--
--   Let $g\in K$ lie in $\mathcal O_{(a,b)}$ for every point $(a,b)$ of the cover. Then $g$ comes from the coordinate ring:
--   $$g\in\bigcap_{\substack{(a,b)\in\mathbb C^2\\ b^n=f(a)}}\mathcal O_{(a,b)}\ \Longrightarrow\ \exists\,r\in R:\ \iota(r)=g.$$
--
--   In the formalization it is applied with $n=4$ to the quartic $x^4+y^4=2$, written $y^4=2-x^4$, to show that $F\,y^3$ comes from the coordinate ring whenever $F\,dx$ is holomorphic; this is a step of the computation of the genus three in Remark 5 of the note.
--
--   **Formalization Note**: the hypotheses $n\ne0$, $f$ squarefree and $\deg f>0$ are instance arguments (`NeZero`, `Fact`). $K$ is an $R$-algebra through $\iota$, and each $\mathcal O_{(a,b)}$ is an $R$-subalgebra of $K$.
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

theorem CurveSymmetry.kummer_mem_range_of_forall_local (g : KummerField n f)
    (hg : ∀ (a b : ℂ) (hb : b ^ n = f.eval a), g ∈ kummerLocalRing a b hb) :
    ∃ r : KummerRing n f, algebraMap (KummerRing n f) (KummerField n f) r = g := by sorry
