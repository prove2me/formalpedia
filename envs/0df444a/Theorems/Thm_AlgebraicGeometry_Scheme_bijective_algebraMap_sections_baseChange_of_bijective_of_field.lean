-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_baseChange_of_bijective_of_field
-- name    : AlgebraicGeometry.Scheme.bijective_algebraMap_sections_baseChange_of_bijective_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/0a24a25a-71b6-56ce-85f1-02eca428c47c
-- title:
--   Bijectivity of A → Γ(X_A,𝒪) under base change
-- statement:
--   Let $k$ be a field and let $\pi\colon X\to\operatorname{Spec} k$ be a morphism of schemes that is separated and quasi-compact. For a morphism $c\colon X\to\operatorname{Spec} R$ and an open $U\subseteq X$, the project's $R$-algebra structure on $\Gamma(X,U)$ is the one attached to the ring map obtained by identifying $R$ with $\Gamma(\operatorname{Spec} R,\top)$ through the inverse of the canonical isomorphism and then applying $c$ on sections over $U$ (the map `c.appLE ⊤ U le_top`). With this $k$-algebra structure on $\Gamma(X,\top)$ coming from $\pi$, assume that the structure map $k\to\Gamma(X,\top)$ is bijective, so that the global functions on $X$ are exactly the constants. Then for every commutative $k$-algebra $A$ the following holds: form the fibre product $X\times_{\operatorname{Spec} k}\operatorname{Spec} A$, the pullback of $\pi$ along $\operatorname{Spec}$ of the structure map $k\to A$, and equip its ring of global sections with the $A$-algebra structure induced in the same way by the second projection to $\operatorname{Spec} A$; then $A\to\Gamma(X\times_{\operatorname{Spec} k}\operatorname{Spec} A,\top)$ is bijective. Both bijectivity hypothesis and conclusion are two-sided, not merely surjectivity.
--
--   This is flat base change for $H^0$ in the case of a field base, where every algebra is flat: the condition $\pi_*\mathcal O_X=\mathcal O_{\operatorname{Spec} k}$ persists after arbitrary base change $\operatorname{Spec} A\to\operatorname{Spec} k$. It is used in the treatment of the relative Picard functor, namely in the recognition of rigidified line bundles and of invertible modules that become trivial after pullback along every point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_baseChange_of_bijective_of_field.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.bijective_algebraMap_sections_baseChange_of_bijective_of_field
    (k : Type u) [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated π] [QuasiCompact π]
    (hX : letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
      Function.Bijective (algebraMap k Γ(X, ⊤)))
    (A : Type u) [CommRing A] [Algebra k A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap k A)) ⊤
    Function.Bijective (algebraMap A Γ(Limits.pullback π (Scheme.TwoAffineOpenCover.specMap k A), ⊤)) := by sorry
