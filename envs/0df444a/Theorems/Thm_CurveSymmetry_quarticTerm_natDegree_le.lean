-- Prove2me | Theorems.Thm_CurveSymmetry_quarticTerm_natDegree_le
-- name    : CurveSymmetry.quarticTerm_natDegree_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:53.649714+00:00
-- url     : https://prove2.me/theorems/7515d711-35a5-4bbe-9dfe-b982949988b2
-- title:
--   Degree bound on $x^4+y^4=2$: if $p\ne0$ and $p(x)\,y^j\,dx/y^3$ is regular at $\mathcal P_\infty$, then $\deg p+j\le1$
-- statement:
--   Let $K=\mathbb C(x)[Y]/(Y^4-(2-x^4))$ be the function field of the quartic $x^4+y^4=2$, written as the Kummer cover $y^4=2-x^4$; here $y\in K$ is the class of $Y$, so that $x^4+y^4=2$ in $K$. For the chart at infinity $x=1/s$, $y=r/s$, let $K'=\mathbb C(s)[T]/(T^4-(2s^4-1))$, with $r$ the class of $T$, so that $r^4=2s^4-1$, and let $\varphi\colon K\to K'$ be the ring homomorphism with $\varphi(q(x))=q(1/s)$ for $q\in\mathbb C(x)$ and $\varphi(y)=r/s$. Fix $\zeta\in\mathbb C$ with $\zeta^4=-1$, so that $(0,\zeta)$ is a point of $r^4=2s^4-1$, and let $\mathcal O'\subseteq K'$ be its local ring: the localization of $\mathbb C[s][T]/(T^4-(2s^4-1))$ at the kernel of the evaluation $s\mapsto0$, $T\mapsto\zeta$, viewed inside $K'$. Put $\mathcal P_\infty=\varphi^{-1}(\mathcal O')$, a valuation ring of $K$ (a place of $K$ over $x=\infty$).
--
--   Let $\Omega_{K/\mathbb C}$ be the $K$-module of Kähler differentials of $K$ over $\mathbb C$, with universal derivation $d\colon K\to\Omega_{K/\mathbb C}$. A differential is *regular at* a valuation ring $\mathcal O$ of $K$ if it is a $\mathbb C$-linear combination of differentials $u\,dv$ with $u,v\in\mathcal O$.
--
--   Let $p\in\mathbb C[x]$ be a nonzero polynomial and $j\ge0$ an integer. If the differential $p(x)\,y^j\,dx/y^3$ is regular at $\mathcal P_\infty$, then
--   $$\deg p+j\le1.$$
--
--   Applied to the four holomorphic pieces $a_j(x)\,y^j\,dx/y^3$ of a holomorphic differential, it leaves $a_2=a_3=0$, $a_1$ constant and $\deg a_0\le1$; this yields the spanning set $dx/y^3$, $x\,dx/y^3$, $dx/y^2$ of the holomorphic differentials and the genus three of the quartic used in Remark 5 of the note.
--
--   **Formalization Note**: $\zeta$ is one fourth root of $-1$, selected by choice, and the statement concerns that root. $\mathcal P_\infty$ is defined as the preimage of the place of $K'$ at $(0,\zeta)$ under the $\mathbb C$-algebra isomorphism $K\to K'$ whose underlying map is $\varphi$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FermatGenus.lean (C. Perassi)

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

theorem CurveSymmetry.quarticTerm_natDegree_le {p : ℂ[X]} (hp : p ≠ 0) {j : ℕ}
    (h : quarticTerm p j • KaehlerDifferential.D ℂ (KummerField 4 fermatQuartic) quarticX ∈ regularAt fermatInfinityPlace) :
    p.natDegree + j ≤ 1 := by sorry
