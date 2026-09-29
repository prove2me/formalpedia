-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_map_eq_of_isPullback_of_faithfullyFlat
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_map_eq_of_isPullback_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/2f5f94f2-d2ec-5243-b0e4-3f2f95419ea9
-- title:
--   Faithfully flat descent of morphisms of invertible modules
-- statement:
--   Let $S \to S'$ be a homomorphism of commutative rings (in a fixed universe) making $S'$ a faithfully flat $S$-module. Let $T, T', T''$ be schemes equipped with morphisms $t : T \to \operatorname{Spec} S$, $t' : T' \to \operatorname{Spec} S'$ and $t'' : T'' \to \operatorname{Spec}(S' \otimes_S S')$, let $p : T' \to T$ make the square formed by $p, t', t$ and $\operatorname{Spec}$ of $S \to S'$ a pullback, and let $q_1, q_2 : T'' \to T'$ make the squares formed with $t''$, $t'$ and $\operatorname{Spec}$ of the two inclusions $S' \to S' \otimes_S S'$ (left and right factor) pullbacks; assume $q_1$ followed by $p$ equals $q_2$ followed by $p$. Let $L, M$ be $\mathcal{O}_T$-modules which are invertible in the sense that every point of $T$ has an open neighbourhood $U$ on which the pullback along the inclusion $U \hookrightarrow T$ is isomorphic to the unit module of $U$. Let $\alpha : p^{*}L \to p^{*}M$ be a morphism whose pullbacks along $q_1$ and $q_2$ agree after the canonical comparison isomorphisms $q_i^{*}p^{*} \cong (q_i \circ p \text{-composite})^{*}$ and the identification of the two composites. Then there is exactly one morphism $\beta : L \to M$ with $p^{*}\beta = \alpha$.
--
--   This is the morphism part of Grothendieck's fpqc descent for quasi-coherent modules, specialised to invertible modules and to a base change along a faithfully flat ring map: $\operatorname{Hom}(L,M)$ is the equaliser of the two pullback maps on $\operatorname{Hom}(p^*L,p^*M)$. It is used in the construction of the relative Picard functor, where it supplies the descent step for `nonempty_iso_of_pullback_locally_iso_of_faithfullyFlat_of_rigidified`; the proof reduces to the bijectivity of the descent-data map for affine flat surjective covers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_map_eq_of_isPullback_of_faithfullyFlat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_map_eq_of_isPullback_of_faithfullyFlat
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {T T' T'' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
    (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (t'' : T'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (q₁ q₂ : T'' ⟶ T')
    (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))))
    (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hq : q₁ ≫ p = q₂ ≫ p)
    (L M : T.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (α : (Scheme.Modules.pullback p).obj L ⟶ (Scheme.Modules.pullback p).obj M)
    (hα : (Scheme.Modules.pullback q₁).map α ≫ ((Scheme.Modules.pullbackComp q₁ p).app M).hom ≫
        ((Scheme.Modules.pullbackCongr hq).app M).hom ≫ ((Scheme.Modules.pullbackComp q₂ p).app M).inv =
      ((Scheme.Modules.pullbackComp q₁ p).app L).hom ≫ ((Scheme.Modules.pullbackCongr hq).app L).hom ≫
        ((Scheme.Modules.pullbackComp q₂ p).app L).inv ≫ (Scheme.Modules.pullback q₂).map α) :
    ∃! β : L ⟶ M, (Scheme.Modules.pullback p).map β = α := by sorry
