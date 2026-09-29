-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_free_finrank_kaehlerH0_eq_finrank_structureSheafH1_and_baseChange_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_free_finrank_kaehlerH0_eq_finrank_structureSheafH1_and_baseChange_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/15e0d25b-f937-557b-a6e6-ea4fad231212
-- title:
--   Čech H⁰(Ω¹) and H¹(𝒪): freeness and base change
-- statement:
--   Let $p$ be a prime and let $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) be the subring of $\mathbf Q$ consisting of those rationals whose denominator is coprime to $p$ (that is, $\mathbf Z_{(p)}$). Let $X$ be a scheme and $c \colon X \to \operatorname{Spec} R$ a morphism that is proper, smooth of relative dimension $1$ and geometrically integral, and let $\mathcal V$ be a two-chart affine cover of $X$: affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = X$ as opens, i.e. $U_0 \sqcup U_1 = \top$, and with $U_0 \cap U_1$ again affine. Write $A_0 = \Gamma(X, U_0)$, $A_1 = \Gamma(X, U_1)$, $A_{01} = \Gamma(X, U_0 \cap U_1)$, viewed as $R$-algebras via $c$, with the two restriction maps to $A_{01}$. The assertion is that there is a natural number $g$ such that: the module $(\mathcal V.\mathrm{kaehlerSections}\ c).H^0$, namely the kernel of the Čech difference map $\Omega[A_0/R] \times \Omega[A_1/R] \to \Omega[A_{01}/R]$, is a free, finite $R$-module of rank $g$; the module $(\mathcal V.\mathrm{structureSheafSections}\ c).H^1$, namely the quotient of $A_{01}$ by the image of the Čech difference map $A_0 \times A_1 \to A_{01}$, is likewise free and finite of rank $g$; and for every commutative ring $A$ with an $R$-algebra structure there are $A$-linear equivalences $A \otimes_R H^0 \simeq \check H^0$ and $A \otimes_R H^1 \simeq \check H^1$ of the corresponding modules formed from the pulled-back cover $\mathcal V.\mathrm{pullback}\ c\ A$ on $X \times_{\operatorname{Spec} R} \operatorname{Spec} A$ together with its projection $\mathrm{pullback.snd}$ to $\operatorname{Spec} A$, each sending $1 \otimes \omega$, respectively $1 \otimes x$, to the image of $\omega$, respectively $x$, under the canonical base-change maps `kaehlerH0baseChangeMap` and `H1baseChangeMap`. Thus the two Čech modules are free of one and the same rank, and both commute with arbitrary base change along $R \to A$.
--
--   This is cohomology and base change for the two sheaves entering Serre duality on a relative curve over $\mathbf Z_{(p)}$, in the explicit two-chart Čech presentation used throughout: freeness over the local base together with compatibility of formation of $\check H^0(\Omega^1)$ and $\check H^1(\mathcal O)$ with base change, and equality of their ranks. It supplies exactly the module-theoretic input (freeness, finiteness, and the base-change isomorphisms) for the Nakayama descent of the integral Serre pairing, and is cited in the construction of Laurent charts and the bijectivity of that pairing for sectional morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_free_finrank_kaehlerH0_eq_finrank_structureSheafH1_and_baseChange_of_smoothOfRelativeDimension_one.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_free_finrank_kaehlerH0_eq_finrank_structureSheafH1_and_baseChange_of_smoothOfRelativeDimension_one
    (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] (𝒱 : X.TwoAffineOpenCover) :
    ∃ g : ℕ,
      Module.Free ↥(GaloisRep.ratLocalizedAt p) (𝒱.kaehlerSections c).H0 ∧ Module.Finite ↥(GaloisRep.ratLocalizedAt p) (𝒱.kaehlerSections c).H0 ∧
      Module.finrank ↥(GaloisRep.ratLocalizedAt p) (𝒱.kaehlerSections c).H0 = g ∧
      Module.Free ↥(GaloisRep.ratLocalizedAt p) (𝒱.structureSheafSections c).H1 ∧ Module.Finite ↥(GaloisRep.ratLocalizedAt p) (𝒱.structureSheafSections c).H1 ∧
      Module.finrank ↥(GaloisRep.ratLocalizedAt p) (𝒱.structureSheafSections c).H1 = g ∧
      ∀ (A : Type) [CommRing A] [Algebra ↥(GaloisRep.ratLocalizedAt p) A],
        (∃ eH0 : A ⊗[↥(GaloisRep.ratLocalizedAt p)] (𝒱.kaehlerSections c).H0 ≃ₗ[A]
            ((𝒱.pullback c A).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) A))).H0,
          ∀ ω, eH0 (1 ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] ω) = Scheme.TwoAffineOpenCover.kaehlerH0baseChangeMap 𝒱 c A ω) ∧
        (∃ eH1 : A ⊗[↥(GaloisRep.ratLocalizedAt p)] (𝒱.structureSheafSections c).H1 ≃ₗ[A]
            ((𝒱.pullback c A).structureSheafSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) A))).H1,
          ∀ x, eH1 (1 ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] x) = Scheme.TwoAffineOpenCover.H1baseChangeMap 𝒱 c A x) := by sorry
