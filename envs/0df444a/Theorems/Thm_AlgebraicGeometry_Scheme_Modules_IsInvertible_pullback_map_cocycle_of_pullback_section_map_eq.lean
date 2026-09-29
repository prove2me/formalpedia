-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_map_cocycle_of_pullback_section_map_eq
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_map_cocycle_of_pullback_section_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/5d44b2b8-79cb-51f5-a0de-0c75a97e7786
-- title:
--   Normalised isomorphism of rigidified line bundles satisfies the cocycle condition
-- statement:
--   Let $S \to S'$ be a homomorphism of commutative rings, and let $t : T \to \operatorname{Spec} S$, $t' : T' \to \operatorname{Spec} S'$ and $t'' : T'' \to \operatorname{Spec}(S' \otimes_S S')$ be schemes over these affine bases. Assume: $p : T' \to T$ together with $t'$ exhibits $T'$ as the pullback of $t$ along $\operatorname{Spec}$ of $S \to S'$; $q_1, q_2 : T'' \to T'$ together with $t''$ exhibit $T''$ as the pullback of $t'$ along $\operatorname{Spec}$ of the two inclusions $S' \to S' \otimes_S S'$ (left and right respectively); $q_1 \ggg p = q_2 \ggg p$; and the ring map $S' \otimes_S S' \to \Gamma(T'', \mathcal O)$ induced by $t''$ on global sections is surjective. Let $e$ be a section of $t$ and $e'$ a section of $t'$ with $e' \ggg p = \operatorname{Spec}(S \to S') \ggg e$. Let $L, M$ be modules on $T$, each invertible in the sense that every point of $T$ has an open neighbourhood $U$ with the pullback along $U \hookrightarrow T$ isomorphic to the unit sheaf of modules on $U$, and let $\tau_L, \tau_M$ be trivialisations of $e^*L$, $e^*M$. Let $\alpha : p^*L \cong p^*M$ be an isomorphism which is normalised in the sense that $e'^*\alpha$ coincides with the composite obtained from the canonical comparison isomorphisms (`pullbackComp`, `pullbackCongr` applied to $e' \ggg p = \operatorname{Spec}(S \to S') \ggg e$) and the pullback along $\operatorname{Spec}(S \to S')$ of $\tau_L$ followed by $\tau_M^{-1}$. Then $q_1^*\alpha$, transported by the canonical identifications $q_1^*p^*M \cong (q_1 \ggg p)^*M \cong (q_2 \ggg p)^*M \cong q_2^*p^*M$, agrees with $q_2^*\alpha$ transported by the corresponding identifications on $L$; that is, the two composites $q_1^*p^*L \to q_2^*p^*M$ are equal.
--
--   This is the cocycle condition of faithfully flat descent for invertible modules, verified for a rigidified (normalised) isomorphism of line bundles after base change along $S \to S'$. It is used in [`AlgebraicGeometry.PolarisedAbelianScheme.nonempty_iso_of_pullback_locally_iso_of_faithfullyFlat_of_rigidified`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.nonempty_iso_of_pullback_locally_iso_of_faithfullyFlat_of_rigidified), where a locally defined isomorphism of rigidified line bundles on an abelian scheme is descended to the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_map_cocycle_of_pullback_section_map_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_map_cocycle_of_pullback_section_map_eq
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S']
    {T T' T'' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
    (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (t'' : T'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (q₁ q₂ : T'' ⟶ T')
    (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))))
    (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hq : q₁ ≫ p = q₂ ≫ p)
    (hΓ'' : Function.Surjective (t''.appTop).hom)
    (e : Spec (CommRingCat.of S) ⟶ T) (he : e ≫ t = 𝟙 _)
    (e' : Spec (CommRingCat.of S') ⟶ T') (he' : e' ≫ t' = 𝟙 _)
    (hpe : e' ≫ p = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ e)
    (L M : T.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (τL : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (τM : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (α : (Scheme.Modules.pullback p).obj L ≅ (Scheme.Modules.pullback p).obj M)
    (hα : (Scheme.Modules.pullback e').map α.hom =
      ((Scheme.Modules.pullbackComp e' p).app L ≪≫ (Scheme.Modules.pullbackCongr hpe).app L ≪≫
        ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap S S'))) e).app L).symm ≪≫
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S S')))).mapIso (τL ≪≫ τM.symm) ≪≫
        (Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap S S'))) e).app M ≪≫
        ((Scheme.Modules.pullbackCongr hpe).app M).symm ≪≫ ((Scheme.Modules.pullbackComp e' p).app M).symm).hom) :
    (Scheme.Modules.pullback q₁).map α.hom ≫ ((Scheme.Modules.pullbackComp q₁ p).app M).hom ≫
        ((Scheme.Modules.pullbackCongr hq).app M).hom ≫ ((Scheme.Modules.pullbackComp q₂ p).app M).inv =
      ((Scheme.Modules.pullbackComp q₁ p).app L).hom ≫ ((Scheme.Modules.pullbackCongr hq).app L).hom ≫
        ((Scheme.Modules.pullbackComp q₂ p).app L).inv ≫ (Scheme.Modules.pullback q₂).map α.hom := by sorry
