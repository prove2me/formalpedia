-- Prove2me | Theorems.Thm_AlgebraicGeometry_bijective_algebraMap_sections_pullback_of_isPullback_of_forall_bijective
-- name    : AlgebraicGeometry.bijective_algebraMap_sections_pullback_of_isPullback_of_forall_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/2b35d1d6-2547-53af-8306-db9a57881caf
-- title:
--   Base change stability of T xrightarrow∼ Γ(A_T)
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism of schemes. Assume (hypothesis `hH0`) that for every commutative ring $T$ carrying an $S$-algebra structure the canonical ring map $T \to \Gamma(A \times_{\operatorname{Spec} S} \operatorname{Spec} T, \top)$ is bijective, where the $T$-algebra structure on the global sections is the one attached by `Scheme.TwoAffineOpenCover.algebraOfHom` to the second projection $A \times_{\operatorname{Spec} S} \operatorname{Spec} T \to \operatorname{Spec} T$ of the pullback of $f$ along $\operatorname{Spec}$ of $S \to T$, i.e. the composite of the inverse of the isomorphism $T \cong \Gamma(\operatorname{Spec} T, \top)$ with the section-level map of that projection from $\top$ to $\top$. Let further $S'$ be a commutative $S$-algebra, $A'$ a scheme, $f' : A' \to \operatorname{Spec} S'$ and $g : A' \to A$ morphisms such that the square with $g$ on top, $f'$ on the left, $f$ on the right and $\operatorname{Spec}$ of $S \to S'$ on the bottom is cartesian. Then for every commutative ring $T$ with an $S'$-algebra structure the corresponding map $T \to \Gamma(A' \times_{\operatorname{Spec} S'} \operatorname{Spec} T, \top)$, formed in the same way from the second projection of the pullback of $f'$ along $\operatorname{Spec}$ of $S' \to T$, is bijective.
--
--   This is the stability under base change of the condition that the ring of global functions on every affine base change of $A \to \operatorname{Spec} S$ is the base ring itself (the $H^0$ condition satisfied, for instance, by proper morphisms with geometrically connected and reduced fibres). It supplies the hypothesis of this shape in the descent and uniqueness arguments for polarisations and in the construction of fake elliptic curves in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_bijective_algebraMap_sections_pullback_of_isPullback_of_forall_bijective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.bijective_algebraMap_sections_pullback_of_isPullback_of_forall_bijective
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (S' : Type u) [CommRing S'] [Algebra S S'] {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of S')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (T : Type u) [CommRing T] [Algebra S' T] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (pullback.snd f' (Scheme.TwoAffineOpenCover.specMap S' T)) ⊤
    Function.Bijective (algebraMap T Γ(pullback f' (Scheme.TwoAffineOpenCover.specMap S' T), ⊤)) := by sorry
