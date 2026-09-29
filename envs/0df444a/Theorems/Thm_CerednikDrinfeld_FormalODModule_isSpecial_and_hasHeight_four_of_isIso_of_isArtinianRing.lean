-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing
-- name    : CerednikDrinfeld.FormalODModule.isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/bc9ae625-ec56-5228-b149-953039dcecdf
-- title:
--   Speciality and height 4 lift along Artinian thickenings
-- statement:
--   Let $q$ be a prime and write $\mathbb Z_{q^2}$ for `Zp2 q`, the Witt vectors of the field with $q^2$ elements. Let $O$ be a commutative local ring with residue field $k$ and residue map $\mathrm{res}_O$, let $\iota\colon\mathbb Z_{q^2}\to O$ be a ring homomorphism, and let $X_0$ be a formal $\mathcal O_D$-module over $k$ for the composite $\mathrm{res}_O\circ\iota$ — that is, a two-dimensional commutative formal group law together with an action of $\mathbb Z_{q^2}$ by endomorphism series and a series $\varpi$ with $\varpi\circ\varpi=[q]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$ — which is special (the submodules `lieZero` and `lieOne` attached to $\mathrm{res}_O\circ\iota$ are complementary and both invertible) and of height $4$ (the series $[q]$ has kernel of degree $q^4$). Let $A$ be a commutative Artinian local $O$-algebra, $\mathrm{res}_A\colon A\to k$ a surjective ring homomorphism with $\mathrm{res}_A\circ(\text{structure map }O\to A)=\mathrm{res}_O$, let $X$ be a formal $\mathcal O_D$-module over $A$, and let $w$ be a homomorphism of formal $\mathcal O_D$-modules from the base change $X\otimes_{\mathrm{res}_A}k$ to $X_0$ admitting a two-sided inverse. Then $X$ is special with respect to $\mathbb Z_{q^2}\to O\to A$ and has height $4$.
--
--   This is the statement that the two conditions cutting out Drinfeld's moduli problem for special formal $\mathcal O_D$-modules of height $4$ — speciality of the Lie algebra decomposition and height $4$ — propagate from the residue field to an Artinian local thickening. It is the deformation-theoretic input for the prorepresentability statements about deformations of special formal $\mathcal O_D$-modules and for the Serre–Tate dictionary for fake elliptic curves in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.FormalODModule.isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing
    {q : ℕ} [Fact q.Prime]
    (O : Type) [CommRing O] [IsLocalRing O]
    (ι : Zp2 q →+* O) (X₀ : SpecialFormalODModule q ((IsLocalRing.residue O).comp ι))
    (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
    (resA : A →+* IsLocalRing.ResidueField O) (hs : Function.Surjective resA)
    (hc : resA.comp (algebraMap O A) = IsLocalRing.residue O)
    (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso) :
    X.IsSpecial ((algebraMap O A).comp ι) ∧ X.HasHeight 4 := by sorry
