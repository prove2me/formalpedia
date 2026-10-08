-- Prove2me | Theorems.Thm_CurveSymmetry_mem_regularAt_familyInfinityPlace_iff
-- name    : CurveSymmetry.mem_regularAt_familyInfinityPlace_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:08.611244+00:00
-- url     : https://prove2.me/theorems/8c19ea64-79bb-424f-b4cf-36bd38a53146
-- title:
--   At the place over $t=\infty$, intrinsic regularity is regularity of the transported differential at $(0,0)$
-- statement:
--   Let $m\ge1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$. Put $h_\alpha(t)=-t(t^m+1)(\alpha t^m+\bar\alpha)\in\mathbb C[t]$ and let $K_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha(t))$, with $w$ the class of $W$, so that $w^2=h_\alpha(t)$; this is the function field of the double cover of the $t$-line in equation (7) of the note, written with $w=t(t^m+1)Y$. Let $\Omega_{K_\alpha/\mathbb C}$ be its module of Kähler differentials, with universal derivation $d$.
--
--   For the conjugate parameter, $K_{\bar\alpha}$ is built in the same way, with coordinate $s$ and root $w'$, where $w'^2=h_{\bar\alpha}(s)=-s(s^m+1)(\bar\alpha s^m+\alpha)$. Since $h_{\bar\alpha}(0)=0$, the point $(0,0)$ lies on the curve $w'^2=h_{\bar\alpha}(s)$; its local ring $\mathcal O'_{(0,0)}\subset K_{\bar\alpha}$, the localization of $\mathbb C[s][W']/(W'^2-h_{\bar\alpha})$ at the maximal ideal of $(0,0)$, is a valuation ring of $K_{\bar\alpha}$. Let $\Phi\colon K_\alpha\to K_{\bar\alpha}$ be the ring isomorphism with $\Phi(t)=1/s$ and $\Phi(w)=w'\,s^{-(m+1)}$ (the chart at $t=\infty$); it is $\mathbb C$-linear. Let $\Phi_\ast\colon\Omega_{K_\alpha/\mathbb C}\to\Omega_{K_{\bar\alpha}/\mathbb C}$ be the induced map on differentials, $\Phi_\ast(g\,dk)=\Phi(g)\,d\Phi(k)$, and let $\mathcal O_\infty=\{\xi\in K_\alpha:\ \Phi(\xi)\in\mathcal O'_{(0,0)}\}$ be the place of $K_\alpha$ over $t=\infty$.
--
--   For a valuation ring $\mathcal O$ of $K_\alpha$ (a subring with $\xi\in\mathcal O$ or $\xi^{-1}\in\mathcal O$ for every nonzero $\xi\in K_\alpha$), write $\operatorname{Reg}(\mathcal O)$ for the space of $\mathbb C$-linear combinations of differentials $a\,db$ with $a,b\in\mathcal O$; $\mathcal O_\infty$ is such a ring. A differential $\eta\in\Omega_{K_{\bar\alpha}/\mathbb C}$ is *regular at* $(0,0)$ if $f\in\mathcal O'_{(0,0)}$ whenever $u\in\mathcal O'_{(0,0)}$ generates the maximal ideal of $\mathcal O'_{(0,0)}$ and $\eta=f\,du$ with $f\in K_{\bar\alpha}$.
--
--   Then, for every $\omega\in\Omega_{K_\alpha/\mathbb C}$,
--
--   $$\omega\in\operatorname{Reg}(\mathcal O_\infty)\iff\Phi_\ast\omega\ \text{is regular at }(0,0).$$
--
--   The right-hand side is the explicit definition of regularity at infinity used for the holomorphic differentials of the family's double cover. Together with the corresponding statement at the finite points, it identifies the intrinsically defined holomorphic differentials of $K_\alpha$ with the explicitly computed ones, in the genus computation of Lemma 4 that is used in Remark 5.
--
--   **Formalization Note**: the hypotheses $m>0$ and $\alpha\ne\bar\alpha$ are `Fact` instances; $|\alpha|=1$ is not assumed.
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

theorem CurveSymmetry.mem_regularAt_familyInfinityPlace_iff (ω : Ω[QuadField (familyH m α)⁄ℂ]) :
    ω ∈ regularAt (familyInfinityPlace m α) ↔ IsRegularAtInfinity ω := by sorry
