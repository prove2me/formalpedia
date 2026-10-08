-- Prove2me | Theorems.Thm_CurveSymmetry_kummer_regularAt_ramified
-- name    : CurveSymmetry.kummer_regularAt_ramified
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:02.331464+00:00
-- url     : https://prove2.me/theorems/a556305d-96b7-4a69-86d8-d6275a9af766
-- title:
--   Regularity of $F\,dx$ at a ramified point of the Kummer cover $y^n=f(x)$
-- statement:
--   Let $n\ge1$ be an integer and let $f\in\mathbb C[x]$ be a squarefree polynomial of positive degree. Let $R=\mathbb C[x][Y]/(Y^n-f)$ be the affine coordinate ring of the Kummer cover $y^n=f(x)$ and $K=\mathbb C(x)[Y]/(Y^n-f)$ its function field (a field, as $Y^n-f$ is irreducible over $\mathbb C(x)$). Write $y\in K$ for the class of $Y$, so that $y^n=f(x)$, and $\iota\colon R\to K$ for the $\mathbb C[x]$-algebra map sending the class of $Y$ to $y$.
--
--   Let $\Omega_{K/\mathbb C}$ be the $K$-module of Kähler differentials of $K$ over $\mathbb C$, with universal derivation $d\colon K\to\Omega_{K/\mathbb C}$. A differential is *regular at* a valuation ring $\mathcal O$ of $K$ if it is a $\mathbb C$-linear combination of differentials $u\,dv$ with $u,v\in\mathcal O$.
--
--   Let $(a,b)\in\mathbb C^2$ be a point of the cover, that is $b^n=f(a)$. Let $\mathrm{ev}_{(a,b)}\colon R\to\mathbb C$ be the evaluation $x\mapsto a$, $Y\mapsto b$, and let $\mathcal O_{(a,b)}\subseteq K$ be the localization of $R$ at $\ker\mathrm{ev}_{(a,b)}$, viewed inside $K$: the quotients $\iota(p)/\iota(q)$ with $p,q\in R$ and $\mathrm{ev}_{(a,b)}(q)\ne0$. It is a valuation ring of $K$, the place of $K$ at $(a,b)$.
--
--   Assume $f(a)=0$ (so that $b=0$). Then for every $F\in K$,
--   $$F\,dx\ \text{is regular at}\ \mathcal O_{(a,b)}\iff F\,y^{\,n-1}\in\mathcal O_{(a,b)}.$$
--
--   This is the companion, at the points over the roots of $f$, of the criterion at the points with $f(a)\ne0$. In the formalization it is applied with $n=4$ to the quartic $x^4+y^4=2$, written $y^4=2-x^4$, at its four points with $x^4=2$, to show that $F\,y^3$ comes from the coordinate ring when $F\,dx$ is holomorphic; this is a step of the computation of the genus three in Remark 5 of the note.
--
--   **Formalization Note**: the hypotheses $n\ne0$, $f$ squarefree and $\deg f>0$ are instance arguments (`NeZero`, `Fact`). The place at $(a,b)$ is a valuation subring of $K$ with the same elements as the localization $\mathcal O_{(a,b)}$.
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

theorem CurveSymmetry.kummer_regularAt_ramified (hfa : f.eval a = 0) (F : KummerField n f) :
    F • KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) ∈ regularAt (kummerPlace a b hb) ↔
      F * AdjoinRoot.root (kummerRat n f) ^ (n - 1) ∈ kummerPlace a b hb := by sorry
