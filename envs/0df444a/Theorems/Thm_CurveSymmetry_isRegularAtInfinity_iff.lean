-- Prove2me | Theorems.Thm_CurveSymmetry_isRegularAtInfinity_iff
-- name    : CurveSymmetry.isRegularAtInfinity_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:27.334688+00:00
-- url     : https://prove2.me/theorems/c1c8624e-35ec-40d1-be39-8ebaf47ed6cf
-- title:
--   Regularity of $f\,dt$ at the place of $K_\alpha$ over $t=\infty$, in terms of the chart at infinity
-- statement:
--   Let $m\ge1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\overline\alpha$, and put $h_\alpha(t)=-t(t^m+1)(\alpha t^m+\overline\alpha)\in\mathbb C[t]$. Let $K_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha)$ be the function field of the double cover $w^2=h_\alpha(t)$, where $t$ and $w$ denote the classes of $t$ and $W$; in the setting of the note this is the function field of $V_\alpha$, read in the chart of equation (7) with $w=t(t^m+1)Y$. Write $\Omega_{K_\alpha/\mathbb C}$ for the $K_\alpha$-vector space of Kähler differentials of $K_\alpha$ over $\mathbb C$ and $dx$ for the differential of $x\in K_\alpha$.
--
--   For the place over $t=\infty$, put $h_{\overline\alpha}(s)=-s(s^m+1)(\overline\alpha s^m+\alpha)$ and let $K_{\overline\alpha}=\mathbb C(s)[W]/(W^2-h_{\overline\alpha})$ be the function field of the conjugate cover ${w'}^2=h_{\overline\alpha}(s)$, where $s$ and $w'$ denote the classes of $s$ and $W$. Since $h_{\overline\alpha}(0)=0$, the point $(s,w')=(0,0)$ lies on this cover; let $\mathcal O'_{(0,0)}\subset K_{\overline\alpha}$ be the localization of $\mathbb C[s][W]/(W^2-h_{\overline\alpha})$ at the maximal ideal of this point (the kernel of $s\mapsto0$, $w'\mapsto0$), a discrete valuation ring, whose *uniformizers* are the generators of its maximal ideal. Let $\varphi\colon K_\alpha\to K_{\overline\alpha}$ be the isomorphism of $\mathbb C$-algebras with $\varphi(t)=1/s$ and $\varphi(w)=w'\,s^{-(m+1)}$, the chart $s=1/t$, $w'=w\,s^{m+1}$ at infinity. The place of $K_\alpha$ over $t=\infty$ has valuation ring $\mathcal O_\infty=\varphi^{-1}(\mathcal O'_{(0,0)})$.
--
--   Differentials of $K_{\overline\alpha}$ are written in the same way, in $\Omega_{K_{\overline\alpha}/\mathbb C}$. A differential $\omega\in\Omega_{K_\alpha/\mathbb C}$ is *regular at infinity* if its transport $\varphi_{\ast}\omega\in\Omega_{K_{\overline\alpha}/\mathbb C}$, determined by $\varphi_{\ast}(g\,dx)=\varphi(g)\,d\varphi(x)$, is regular at $(0,0)$: for every uniformizer $u'$ of $\mathcal O'_{(0,0)}$ and every $g'\in K_{\overline\alpha}$ with $\varphi_{\ast}\omega=g'\,du'$ one has $g'\in\mathcal O'_{(0,0)}$.
--
--   Let $h_{\overline\alpha}'$ be the derivative of $h_{\overline\alpha}$. For every $f\in K_\alpha$,
--   $$f\,dt\text{ is regular at infinity}\iff\varphi(f)\cdot\frac{-2w'}{s^2\,h_{\overline\alpha}'(s)}\in\mathcal O'_{(0,0)}.$$
--
--   The element on the right is the coefficient of the transported differential $\varphi_{\ast}(f\,dt)$ against the uniformizer $w'$ of $\mathcal O'_{(0,0)}$. This is the regularity criterion at the place over $t=\infty$, which is then simplified to the condition $\varphi(f)/{w'}^3\in\mathcal O'_{(0,0)}$; in this way it enters the formal proof of the genus clause of Lemma 4 of the note (the normalization of $V_\alpha$ has genus $m$) and, through the case $m=2$, of Remark 5.
--
--   **Formalization Note**: the hypotheses $m\ge1$ and $\alpha\ne\overline\alpha$ are `Fact` instances; the condition $|\alpha|=1$ of the note is not assumed. In the formal statement the coefficient appears as $\varphi(f)\cdot\bigl(s^2h_{\overline\alpha}'(s)\bigr)^{-1}\cdot(-2w')$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Lemma 4, pp. 3-4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/InfinityRegularity.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
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
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

theorem CurveSymmetry.isRegularAtInfinity_iff (f : QuadField (familyH m α)) :
    IsRegularAtInfinity (f • KaehlerDifferential.D ℂ (QuadField (familyH m α))
        (quadT (familyH m α))) ↔
      familyInfinityMap m α f *
          ((quadT (familyH m (star α)) ^ 2 *
            algebraMap ℂ[X] (QuadField (familyH m (star α)))
              (familyH m (star α)).derivative)⁻¹ *
            -(2 * AdjoinRoot.root (quadRat (familyH m (star α))))) ∈
        quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α) := by sorry
