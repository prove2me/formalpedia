-- Prove2me | Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_map_pullback_of_comm_sq
-- name    : AlgebraicGeometry.DescentCharacter.hasValue_map_pullback_of_comm_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/8479de8c-8574-5d6d-8c66-606eafbe2036
-- title:
--   Base change of descent-character values along commuting squares
-- statement:
--   Let $X,Y,X',Y'$ be schemes and $R,R'$ commutative rings, with morphisms $f\colon X\to\operatorname{Spec}R$ and $f'\colon X'\to\operatorname{Spec}R'$ and a ring homomorphism $\varphi\colon R\to R'$. Suppose given $T\colon X\to X$ and $q\colon X\to Y$ with $T\gg q=q$, and likewise $T'\colon X'\to X'$, $q'\colon X'\to Y'$ with $T'\gg q'=q'$, together with $g_X\colon X'\to X$, $g_Y\colon Y'\to Y$ satisfying $g_X\gg q=q'\gg g_Y$, $T'\gg g_X=g_X\gg T$ and $g_X\gg f=f'\gg\operatorname{Spec}(\varphi)$. Let $N,M$ be modules on $Y$ and $\beta\colon q^{*}N\xrightarrow{\ \sim\ }q^{*}M$ an isomorphism, and let $c\in R$ be such that `HasValue f h β c` holds: on every open $U\subseteq X$ the component at $U$ of the discrepancy $\beta^{-1}\ggg\,(\text{translate of }\beta\text{ along }T)$, an automorphism of $q^{*}M$, is multiplication by the section `baseSection f c U`. The conclusion is that the same property, with $f'$, $T'$, $q'$ and the element $\varphi(c)$, holds for the isomorphism between the pullbacks of $N$ and of $M$ from $Y$ to $X'$ along $g_Y$ and $q'$ obtained from `(Scheme.Modules.pullback gX).mapIso β` by conjugating with the canonical comparison isomorphisms `Scheme.Modules.pullbackComp` for pullback along composites and `Scheme.Modules.pullbackCongr` applied to $g_X\gg q=q'\gg g_Y$ and to its symmetric form.
--
--   This is the functoriality, or base-change naturality, of the descent character: the $R$-valued invariant attached to an isomorphism between pullbacks along $q$ together with a self-map $T$ over $q$ is carried by a commuting square of such data to the corresponding invariant over $R'$, pushed forward along $\varphi$. It is used in the construction of the torsion character of $2$-torsion line bundles, where it supplies the compatibility of the value with change of base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_DescentCharacter_hasValue_map_pullback_of_comm_sq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

theorem AlgebraicGeometry.DescentCharacter.hasValue_map_pullback_of_comm_sq
    {X Y X' Y' : Scheme.{u}} {R R' : Type u} [CommRing R] [CommRing R']
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : R →+* R')
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {T' : X' ⟶ X'} {q' : X' ⟶ Y'} (h' : T' ≫ q' = q')
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) (hq : gX ≫ q = q' ≫ gY) (hT : T' ≫ gX = gX ≫ T)
    (hf : gX ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    {N M : Y.Modules} (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (c : R) (hβ : HasValue f h β c) :
    HasValue f' h'
      ((Scheme.Modules.pullbackComp q' gY).app N ≪≫ (Scheme.Modules.pullbackCongr hq.symm).app N ≪≫
        ((Scheme.Modules.pullbackComp gX q).app N).symm ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫
        (Scheme.Modules.pullbackComp gX q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫
        ((Scheme.Modules.pullbackComp q' gY).app M).symm)
      (φ c) := by sorry
