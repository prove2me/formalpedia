-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_cotangent_sectionAlgHom
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_cotangent_sectionAlgHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/3ea195f3-7f51-54c8-807f-25b0efea27cf
-- title:
--   Conormal module of a section of a smooth relative curve is free of rank one
-- statement:
--   Let $R$ be a commutative local ring, let $X$ be a scheme, and let $\mathcal{V}$ be a two-affine open cover of $X$, that is, a pair of opens $U_0, U_1 \subseteq X$, both affine, with affine intersection $U_0 \cap U_1$ and with $U_0 \cup U_1 = X$. Let $c \colon X \to \operatorname{Spec} R$ be smooth of relative dimension $1$, so that in particular $\Gamma(X, U_0)$ is an $R$-algebra via the map $R \cong \Gamma(\operatorname{Spec} R, \top) \to \Gamma(X, U_0)$ obtained from $c$. Let $\sigma \colon \operatorname{Spec} R \to X$ satisfy $\sigma$ followed by $c$ equal to the identity of $\operatorname{Spec} R$, and assume the set-theoretic image of $\sigma$ on points is contained in $U_0$. Then $\sigma$ induces an $R$-algebra homomorphism $\sigma^{*} \colon \Gamma(X, U_0) \to R$, namely the map on sections $\Gamma(X,U_0) \to \Gamma(\operatorname{Spec} R, \top) \cong R$ attached to $\sigma$, and the assertion is that for $I = \ker(\sigma^{*})$ the $R$-module $I/I^{2}$ is free and its rank over $R$ equals $1$.
--
--   This is the statement that the conormal module of a section of a smooth morphism of relative dimension $1$ over a local base is free of rank one, in the affine-chart form needed here; both local freeness (smoothness of $c$) and triviality of the line bundle ($R$ local) enter. It is used to produce a local parameter along the section, and is cited in the construction of Laurent charts and completions along a section for smooth proper curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_cotangent_sectionAlgHom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_cotangent_sectionAlgHom {R : Type u} [CommRing R] [IsLocalRing R] {X : AlgebraicGeometry.Scheme.{u}}
    {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ AlgebraicGeometry.Spec (.of R)}
    [AlgebraicGeometry.SmoothOfRelativeDimension 1 c]
    (σ : AlgebraicGeometry.Spec (.of R) ⟶ X) (hσ : σ ≫ c = 𝟙 _) (hU : Set.range σ.base ⊆ (𝒱.U0 : Set X)) :
    Module.Free R (RingHom.ker
        (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom σ hσ hU).toRingHom).Cotangent ∧
      Module.finrank R (RingHom.ker
        (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom σ hσ hU).toRingHom).Cotangent = 1 := by sorry
