-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
-- name    : AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/080d282b-4ed8-563d-a131-37b0b0164810
-- title:
--   Closed immersion after base change descends to a finitely generated subalgebra
-- statement:
--   Let $A_0$ be a commutative ring and $A$ an $A_0$-algebra, and let $m \colon W \to V$ and $v \colon V \to \operatorname{Spec} A_0$ be morphisms of schemes with $v$ quasi-compact and $m$ quasi-compact, quasi-separated and locally of finite type. For an $A_0$-algebra $B$, form the pullbacks of $m \circ v \colon W \to \operatorname{Spec} A_0$ and of $v$ along $\operatorname{Spec}$ of the structure map $A_0 \to B$, and call a morphism $m_B$ between them a base change of $m$ when $m_B$ followed by the first projection equals the first projection followed by $m$, and $m_B$ followed by the second projection equals the second projection. The hypothesis is that every such morphism $m_A$ for $B = A$ is a closed immersion. The conclusion: for every finite subset $s$ of $A$ there is an $A_0$-subalgebra $T \subseteq A$ which is finitely generated (in the sense of `Subalgebra.FG`) and contains $s$, such that every morphism $m_T$ satisfying the two compatibilities above for $B = T$ is a closed immersion. Both hypothesis and conclusion are stated as universally quantified over all morphisms with the stated compatibilities, so no particular choice of base-change morphism need be produced.
--
--   This is the standard limit argument of Grothendieck's EGA IV, Théorème 8.10.5, in the form: being a closed immersion after base change to $A$ is already achieved after base change to some finitely generated $A_0$-subalgebra of $A$ containing a prescribed finite set. It is the variant of [`AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map`](thm.html#AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map) in which the affineness of the target $V$ is weakened to quasi-compactness of $V$ over $\operatorname{Spec} A_0$, the shape needed when $V$ is an abelian scheme; it is used in the descent to finitely generated subalgebras for polarised abelian schemes, for closed subschemes of projective space, and in the spreading-out of smooth proper morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {W V : Scheme.{u}} (m : W ⟶ V) (v : V ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact v]
    [QuasiCompact m] [QuasiSeparated m] [LocallyOfFiniteType m]
    (hA : ∀ mA : pullback (m ≫ v) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
        pullback v (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))),
      mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m → mA ≫ pullback.snd _ _ = pullback.snd _ _ →
      IsClosedImmersion mA)
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ mT : pullback (m ≫ v) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
          pullback v (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
        mT ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m → mT ≫ pullback.snd _ _ = pullback.snd _ _ →
        IsClosedImmersion mT := by sorry
