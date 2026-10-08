-- Prove2me | Theorems.Thm_CurveSymmetry_familyInfinityPlace_eq_comap
-- name    : CurveSymmetry.familyInfinityPlace_eq_comap
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:49.167233+00:00
-- url     : https://prove2.me/theorems/9b7bec2e-bd7b-47b6-b262-2de0deb7455e
-- title:
--   The place over $t=\infty$ is the pull-back of the point $(0,0)$ of the conjugate cover along the chart isomorphism
-- statement:
--   Let $m\ge1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$. Put $h_\alpha(t)=-t(t^m+1)(\alpha t^m+\bar\alpha)\in\mathbb C[t]$ and let $K_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha(t))$, with $w$ the class of $W$, so that $w^2=h_\alpha(t)$; this is the function field of the double cover of the $t$-line in equation (7) of the note, written with $w=t(t^m+1)Y$. Let $\Omega_{K_\alpha/\mathbb C}$ be its module of Kähler differentials, with universal derivation $d$.
--
--   For the conjugate parameter, $K_{\bar\alpha}$ is built in the same way, with coordinate $s$ and root $w'$, where $w'^2=h_{\bar\alpha}(s)=-s(s^m+1)(\bar\alpha s^m+\alpha)$. Since $h_{\bar\alpha}(0)=0$, the point $(0,0)$ lies on the curve $w'^2=h_{\bar\alpha}(s)$; its local ring $\mathcal O'_{(0,0)}\subset K_{\bar\alpha}$, the localization of $\mathbb C[s][W']/(W'^2-h_{\bar\alpha})$ at the maximal ideal of $(0,0)$, is a valuation ring of $K_{\bar\alpha}$. Let $\Phi\colon K_\alpha\to K_{\bar\alpha}$ be the ring isomorphism with $\Phi(t)=1/s$ and $\Phi(w)=w'\,s^{-(m+1)}$ (the chart at $t=\infty$); it is $\mathbb C$-linear. The place of $K_\alpha$ over $t=\infty$ is defined as the preimage $\mathcal O_\infty=\{\xi\in K_\alpha:\ \Phi(\xi)\in\mathcal O'_{(0,0)}\}$, with $\Phi$ taken as a ring homomorphism.
--
--   The statement is that $\mathcal O_\infty$ is also the preimage of $\mathcal O'_{(0,0)}$ under $\Phi$ regarded as an isomorphism of $\mathbb C$-algebras:
--
--   $$\mathcal O_\infty=\Phi^{-1}\bigl(\mathcal O'_{(0,0)}\bigr).$$
--
--   This is a bookkeeping step: it presents the place over $t=\infty$ as a pull-back along an isomorphism of $\mathbb C$-algebras, the form in which regularity of differentials can be transported along $\Phi$. It is used to show that intrinsic regularity at $\mathcal O_\infty$ is regularity at infinity in the explicit sense, in the genus computation for the family's function field (Lemma 4, Remark 5).
--
--   **Formalization Note**: in Lean, $\mathcal O_\infty$ is defined as the preimage of a valuation subring along $\Phi$ given as a ring homomorphism, while the statement takes the preimage along $\Phi$ bundled as an isomorphism of $\mathbb C$-algebras, with the same underlying map; the content is that these two presentations agree. The hypotheses $m>0$ and $\alpha\ne\bar\alpha$ are `Fact` instances.
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

theorem CurveSymmetry.familyInfinityPlace_eq_comap :
    familyInfinityPlace m α =
      (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).comap
        (familyInfinityAlgEquiv m α :
          QuadField (familyH m α) →+* QuadField (familyH m (star α))) := by sorry
