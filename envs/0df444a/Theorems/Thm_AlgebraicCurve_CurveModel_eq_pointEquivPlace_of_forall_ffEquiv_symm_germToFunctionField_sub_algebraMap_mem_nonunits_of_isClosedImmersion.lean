-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_eq_pointEquivPlace_of_forall_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_of_isClosedImmersion
-- name    : AlgebraicCurve.CurveModel.eq_pointEquivPlace_of_forall_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/81689e89-eecc-5a43-8795-edea3d6f7040
-- title:
--   A place determined by its readings on an affine chart
-- statement:
--   Let $R_0$ be a commutative ring, $K$ an algebraically closed field, $\mathrm{toK} : R_0 \to K$ a ring homomorphism, and $g : Y \to \operatorname{Spec} R_0$ a scheme over $R_0$ equipped with an open immersion $\iota : \operatorname{Spec} B \to Y$ from the spectrum of a commutative ring $B$. Let $L$ be a field extension of $K$ and $N$ a curve model of $L/K$: an integral scheme $N.C$ with a proper morphism $N.\mathrm{toBase} : N.C \to \operatorname{Spec} K$ that is smooth of relative dimension $1$, a ring isomorphism $N.\mathrm{ffEquiv} : L \cong N.C.\mathrm{functionField}$ carrying $K$ to the germs at the generic point of the structure morphism, a bijection $N.\mathrm{placeOfPoint}$ from the closed points of $N.C$ to the places of $L/K$ (valuation subrings of $L$ containing $K$, not equal to $L$, and principal ideal rings) such that for each closed point the image in $L$ of the stalk is the valuation subring of its place, and the property that every finite set of points of $N.C$ lies in an affine open. Assume given a closed immersion $h : N.C \to Y \times_{\operatorname{Spec} R_0} \operatorname{Spec} K$ with $h$ followed by the second projection equal to $N.\mathrm{toBase}$, and put $f : N.C \to Y$ for $h$ followed by the first projection (passed as a hypothesis $hf$ rather than a definition), the open subscheme $f^{-1}(\iota(\operatorname{Spec} B))$ of $N.C$ being assumed nonempty. Let $z$ be a section of $N.\mathrm{toBase}$, i.e. a $K$-point of $N.C$, and $\beta : B \to K$ a ring homomorphism such that $z$ followed by $f$ equals $\operatorname{Spec}\beta$ followed by $\iota$. Finally let $Q$ be a place of $L/K$ such that for every $b \in B$ the element of $L$ obtained by transporting along $N.\mathrm{ffEquiv}^{-1}$ the germ at the generic point of the pull-back along $f$ of the section of $Y$ over $\iota(\operatorname{Spec} B)$ corresponding to $b$, minus $\beta(b)$ viewed in $L$, is a nonunit of the valuation subring of $Q$. Then $Q$ is the place attached to $z$ by $N.\mathrm{pointEquivPlace}$, the composite of the bijection between $K$-points and closed points of $N.C$ with $N.\mathrm{placeEquiv}$.
--
--   This is a recognition criterion for places on a smooth proper curve model: a place whose maximal ideal contains the differences between the readings of all chart functions and their values at a given $K$-point is the place of that point. It is used in the analysis of the model of $X_1(p)$, where the curve model arises as a component of a geometric special fibre mapping into a base scheme by a closed immersion onto its image in the base change of an affine chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_eq_pointEquivPlace_of_forall_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_of_isClosedImmersion.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.eq_pointEquivPlace_of_forall_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_of_isClosedImmersion
    {R₀ : Type u} [CommRing R₀] {K : Type u} [Field K] [IsAlgClosed K] (toK : R₀ →+* K)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R₀))
    {B : Type u} [CommRing B] (ι : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion ι]
    {L : Type v} [Field L] [Algebra K L] (N : CurveModel K L)
    (h : N.C ⟶ pullback g (Spec.map (CommRingCat.ofHom toK))) [IsClosedImmersion h]
    (hh : h ≫ pullback.snd _ _ = N.toBase)

    (f : N.C ⟶ Y) (hf : h ≫ pullback.fst _ _ = f)
    [Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ (ι ''ᵁ ⊤)))]
    (z : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}) (β : B →+* K)
    (hz : z.1 ≫ f = Spec.map (CommRingCat.ofHom β) ≫ ι)
    (Q : Place K L)
    (hQ : ∀ b : B, N.ffEquiv.symm (N.C.germToFunctionField (f ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((f.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)))) -
      algebraMap K L (β b) ∈ Q.toValuationSubring.nonunits) :
    Q = N.pointEquivPlace z := by sorry
