-- Prove2me | Theorems.Thm_CurveSymmetry_infinity_val_s
-- name    : CurveSymmetry.infinity_val_s
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:42:06.134911+00:00
-- url     : https://prove2.me/theorems/8646a70a-2c6f-438d-8b39-e0a935c7a0d1
-- title:
--   At the point $(0,0)$ of $w'^2=-s(s^m+1)(\bar\alpha s^m+\alpha)$, the valuation satisfies $v(s)=v(w')^2$
-- statement:
--   Let $m\ge1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$. Consider the double cover attached to the conjugate parameter: $K_{\bar\alpha}=\mathbb C(s)[W']/(W'^2-h_{\bar\alpha}(s))$, where $h_{\bar\alpha}(s)=-s(s^m+1)(\bar\alpha s^m+\alpha)$, with $w'$ the class of $W'$, so that $w'^2=h_{\bar\alpha}(s)$. Since $h_{\bar\alpha}(0)=0$, the point $(0,0)$ lies on the affine curve $w'^2=h_{\bar\alpha}(s)$. Its local ring $\mathcal O'_{(0,0)}\subset K_{\bar\alpha}$, the localization of $\mathbb C[s][W']/(W'^2-h_{\bar\alpha})$ at the maximal ideal of $(0,0)$, is a valuation ring of $K_{\bar\alpha}$; let $v$ be its valuation.
--
--   Then
--
--   $$v(s)=v(w')^{2}.$$
--
--   The function field $K_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha(t))$ of the family's double cover, with $h_\alpha(t)=-t(t^m+1)(\alpha t^m+\bar\alpha)$ and $w^2=h_\alpha(t)$, is identified with $K_{\bar\alpha}$ by $t=1/s$, $w=w'\,s^{-(m+1)}$, and its place over $t=\infty$ is the preimage of $\mathcal O'_{(0,0)}$. The identity is used in the comparison of valuations at that place which shows that every holomorphic $f\,dt$ on $K_\alpha$ equals $a(t)\,dt/w$ with $\deg a<m$, a step of the genus computation in Lemma 4.
--
--   **Formalization Note**: $v$ is Mathlib's valuation of the valuation subring, written multiplicatively with values in its value group, so that $v(\xi)\le1$ exactly for $\xi$ in the ring. In additive notation the statement says that $s$ vanishes at $(0,0)$ to twice the order of $w'$. The hypotheses $m>0$ and $\alpha\ne\bar\alpha$ are `Fact` instances.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Lemma 4, pp. 3-4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/HolomorphicSpan.lean (C. Perassi)

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
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

theorem CurveSymmetry.infinity_val_s :
    (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
        (quadT (familyH m (star α))) =
      (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
        (AdjoinRoot.root (quadRat (familyH m (star α)))) ^ 2 := by sorry
