-- Prove2me | Theorems.Thm_CurveSymmetry_family_holomorphicSpace_eq
-- name    : CurveSymmetry.family_holomorphicSpace_eq
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:29.739818+00:00
-- url     : https://prove2.me/theorems/97c87654-e131-4e91-b845-1762df877c2a
-- title:
--   Intrinsic and place-by-place holomorphic differentials agree on $w^2=-t(t^m+1)(\alpha t^m+\bar\alpha)$
-- statement:
--   Let $m\ge1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$. Put $h_\alpha(t)=-t(t^m+1)(\alpha t^m+\bar\alpha)\in\mathbb C[t]$ and let $K_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha(t))$, with $w$ the class of $W$, so that $w^2=h_\alpha(t)$; this is the function field of the double cover of the $t$-line in equation (7) of the note, written with $w=t(t^m+1)Y$. Let $\Omega_{K_\alpha/\mathbb C}$ be its module of Kähler differentials, with universal derivation $d$. For a point $(t_0,w_0)\in\mathbb C^2$ of the affine curve $w^2=h_\alpha(t)$, that is, with $w_0^2=h_\alpha(t_0)$, let $\mathcal O_{(t_0,w_0)}\subset K_\alpha$ be its local ring: the localization of $\mathbb C[t][W]/(W^2-h_\alpha)$ at the maximal ideal of $(t_0,w_0)$, viewed inside $K_\alpha$.
--
--   For the conjugate parameter, $K_{\bar\alpha}$ is built in the same way, with coordinate $s$ and root $w'$, where $w'^2=h_{\bar\alpha}(s)=-s(s^m+1)(\bar\alpha s^m+\alpha)$. Since $h_{\bar\alpha}(0)=0$, the point $(0,0)$ lies on the curve $w'^2=h_{\bar\alpha}(s)$; let $\mathcal O'_{(0,0)}\subset K_{\bar\alpha}$ be its local ring there. Let $\Phi\colon K_\alpha\to K_{\bar\alpha}$ be the isomorphism of $\mathbb C$-algebras with $\Phi(t)=1/s$ and $\Phi(w)=w'\,s^{-(m+1)}$ (the chart at $t=\infty$), and let $\Phi_\ast\colon\Omega_{K_\alpha/\mathbb C}\to\Omega_{K_{\bar\alpha}/\mathbb C}$ be the induced map, $\Phi_\ast(g\,dk)=\Phi(g)\,d\Phi(k)$.
--
--   A differential $\omega\in\Omega_{K_\alpha/\mathbb C}$ is *regular at* a point $(t_0,w_0)$ if $f\in\mathcal O_{(t_0,w_0)}$ whenever $u\in\mathcal O_{(t_0,w_0)}$ generates the maximal ideal of $\mathcal O_{(t_0,w_0)}$ and $\omega=f\,du$ with $f\in K_\alpha$. It is *regular at infinity* if $\Phi_\ast\omega$ is regular, in the same sense, at the point $(0,0)$ of $w'^2=h_{\bar\alpha}(s)$. It is *holomorphic* if it is regular at every point $(t_0,w_0)$ of $w^2=h_\alpha(t)$ and at infinity. The holomorphic differentials form a complex vector subspace $\mathcal H_\alpha\subseteq\Omega_{K_\alpha/\mathbb C}$.
--
--   Intrinsically, a *place* of $K_\alpha$ is a valuation ring $\mathcal O\ne K_\alpha$ of $K_\alpha$ (a subring with $\xi\in\mathcal O$ or $\xi^{-1}\in\mathcal O$ for every nonzero $\xi\in K_\alpha$) that contains $\mathbb C$; a differential is *regular at* $\mathcal O$ if it is a $\mathbb C$-linear combination of differentials $a\,db$ with $a,b\in\mathcal O$; and $H(K_\alpha)\subseteq\Omega_{K_\alpha/\mathbb C}$ is the space of differentials regular at every place of $K_\alpha$.
--
--   Then
--
--   $$H(K_\alpha)=\mathcal H_\alpha.$$
--
--   That is, a differential of $K_\alpha$ is regular at every place of $K_\alpha$ if and only if it is regular at every point $(t_0,w_0)$ and at infinity in the explicit sense above.
--
--   So the genus of $K_\alpha$ in the intrinsic sense, $\dim_{\mathbb C}H(K_\alpha)$, equals $\dim_{\mathbb C}\mathcal H_\alpha=m$. Transported to the function field of $P_\alpha=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$, this gives the genus clause of Lemma 4 and the genus two of the $m=2$ family in Remark 5.
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

theorem CurveSymmetry.family_holomorphicSpace_eq :
    holomorphicSpace (QuadField (familyH m α)) = holomorphicDifferentials m α := by sorry
