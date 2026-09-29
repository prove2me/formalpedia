-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map
-- name    : AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/62f6a7db-617b-5f4a-92e3-560f4f7a6869
-- title:
--   Closed immersions descend to a finitely generated subalgebra
-- statement:
--   Let $A_0$ be a commutative ring and $A$ an $A_0$-algebra, let $V$ be an affine scheme equipped with a morphism $v \colon V \to \operatorname{Spec} A_0$, and let $m \colon W \to V$ be a quasi-compact, quasi-separated morphism that is locally of finite type. For an $A_0$-algebra $B$, consider the two pullbacks $\operatorname{pullback}(m \circ v, \operatorname{Spec}(A_0 \to B))$ and $\operatorname{pullback}(v, \operatorname{Spec}(A_0 \to B))$, i.e. the base changes $W_B$ and $V_B$ along $\operatorname{Spec} B \to \operatorname{Spec} A_0$; a morphism $W_B \to V_B$ whose composite with the first projection equals the first projection followed by $m$, and whose composite with the second projection equals the second projection, is exactly the base change $m_B$ of $m$ (such a morphism exists and is unique by the universal property, so the quantifications below are over this single morphism). The hypothesis is that every such morphism $W_A \to V_A$ is a closed immersion. The conclusion: for every finite subset $s$ of $A$ there is a subalgebra $T \subseteq A$ over $A_0$ which is finitely generated and contains $s$, such that every morphism $W_T \to V_T$ compatible with $m$ on the first projections and with the identity on the second projections is a closed immersion.
--
--   This is the standard descent of the property of being a closed immersion from an inductive limit of base rings to a finitely generated stage, in the style of EGA IV₃ 8.10.5: the base change of a finite-type morphism over an affine base is a closed immersion already over some finitely generated subalgebra containing a prescribed finite set. It is obtained from the corresponding statements for affineness of the pullback and for surjectivity of the induced map on coordinate rings, and it feeds the quasi-compact variant and the descent of separatedness for the second projection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {W V : Scheme.{u}} (m : W ⟶ V) (v : V ⟶ Spec (CommRingCat.of A₀)) [IsAffine V]
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
