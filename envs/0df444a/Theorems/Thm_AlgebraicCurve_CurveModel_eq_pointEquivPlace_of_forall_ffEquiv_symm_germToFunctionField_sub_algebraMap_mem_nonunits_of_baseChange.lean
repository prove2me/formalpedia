-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_eq_pointEquivPlace_of_forall_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_of_baseChange
-- name    : AlgebraicCurve.CurveModel.eq_pointEquivPlace_of_forall_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_of_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/f3e4e7dc-4134-5a8b-bf9d-d0d5323d0532
-- title:
--   Recognising a place from chart coordinates at a K-point
-- statement:
--   Let $R_0$ be a commutative ring, $K$ an algebraically closed field and $toK : R_0 \to K$ a ring homomorphism; let $g : Y \to \operatorname{Spec} R_0$ be a scheme over $R_0$ and $\iota : \operatorname{Spec} B \to Y$ an open immersion for a commutative ring $B$. Let $L$ be a field with a $K$-algebra structure and $N$ a `CurveModel K L`, that is: an integral scheme $N.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} K$ via $N.toBase$, a ring isomorphism $N.ffEquiv : L \cong K(N.C)$ carrying $\operatorname{algebraMap} K L$ to the germ at the generic point of the structure map, a bijection $N.placeOfPoint$ from the closed points of $N.C$ onto the places of $L/K$ (valuation subrings of $L$ containing $K$, proper, and principal ideal rings) such that the image of the stalk at a closed point inside $L$ under $N.ffEquiv^{-1}$ is exactly the corresponding valuation subring, together with the property that every finite set of points of $N.C$ lies in an affine open. Let $e : N.C \to Y \times_{\operatorname{Spec} R_0} \operatorname{Spec} K$ be an isomorphism with $e$ followed by the second projection equal to $N.toBase$, and assume the open subscheme $U = (e \text{ followed by } \mathrm{pr}_1)^{-1}(\iota(\top))$ of $N.C$ is nonempty. Let $z$ be a $K$-point of $N.C$, i.e. a morphism $\operatorname{Spec} K \to N.C$ sectioning $N.toBase$, and $\beta : B \to K$ a ring homomorphism such that $z$ followed by $e$ and $\mathrm{pr}_1$ equals $\operatorname{Spec}\beta$ followed by $\iota$. Finally let $Q$ be a place of $L/K$ such that for every $b \in B$ the element of $L$ obtained by transporting $b$ to a section of $\mathcal{O}_Y$ over $\iota(\top)$, pulling it back along $e$ followed by $\mathrm{pr}_1$ to a section over $U$, taking its germ in $K(N.C)$ and applying $N.ffEquiv^{-1}$, minus $\operatorname{algebraMap} K L(\beta b)$, lies in the nonunits of $Q.toValuationSubring$. Then $Q$ equals the place $N.pointEquivPlace\, z$ attached to $z$, namely $N.placeOfPoint$ of the closed point corresponding to the $K$-point $z$.
--
--   This is a recognition criterion: a place of the function field at which every coordinate function of an affine chart of the model is congruent, modulo the maximal ideal, to its value at a given $K$-point must be the place of that point. It is applied in the analysis of integral models of modular curves at a prime, where places are identified with specialisations of points on a chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_eq_pointEquivPlace_of_forall_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_of_baseChange.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.eq_pointEquivPlace_of_forall_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_of_baseChange
    {R₀ : Type u} [CommRing R₀] {K : Type u} [Field K] [IsAlgClosed K] (toK : R₀ →+* K)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R₀))
    {B : Type u} [CommRing B] (ι : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion ι]
    {L : Type v} [Field L] [Algebra K L] (N : CurveModel K L)
    (e : N.C ⟶ pullback g (Spec.map (CommRingCat.ofHom toK))) [IsIso e]
    (he : e ≫ pullback.snd _ _ = N.toBase)
    [Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)))]
    (z : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}) (β : B →+* K)
    (hz : z.1 ≫ e ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom β) ≫ ι)
    (Q : Place K L)
    (hQ : ∀ b : B, N.ffEquiv.symm (N.C.germToFunctionField ((e ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤))
        (((e ≫ pullback.fst _ _).app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)))) -
      algebraMap K L (β b) ∈ Q.toValuationSubring.nonunits) :
    Q = N.pointEquivPlace z := by sorry
