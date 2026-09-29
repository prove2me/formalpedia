-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/288c3a51-cf74-5886-b58b-2ca70bdf4c0d
-- title:
--   Extending a relative effective Cartier divisor over a DVR
-- statement:
--   Let $f \colon \mathcal C \to S$ be a proper morphism of schemes, let $O$ be a discrete valuation domain, let $g \colon \operatorname{Spec} O \to S$ be a morphism, and let $T'$ be a field which is an $O$-algebra realising $T'$ as the fraction field of $O$; write $\psi = \operatorname{Spec}$ of the structure map $O \to T'$ and let $g_T \colon \operatorname{Spec} T' \to S$ satisfy $g_T = g \circ \psi$. Let $r \in \mathbb N$ and let $E$ be a `RelEffCartierDiv f r gT`, i.e. an ideal sheaf datum $E.I$ on $\mathcal C \times_S \operatorname{Spec} T'$ whose associated closed immersion followed by the projection to $\operatorname{Spec} T'$ is finite, flat and locally of finite presentation with $\operatorname{finrank}$ equal to $r$ at every point of $\operatorname{Spec} T'$. Let $J$ be an ideal sheaf datum on $\mathcal C \times_S \operatorname{Spec} O$ such that the closed immersion it defines, followed by the projection to $\operatorname{Spec} O$, is flat, and assume that the pullback of $J$ along `mapOnProdOver f ψ hψ` (the base-change map $\mathcal C \times_S \operatorname{Spec} T' \to \mathcal C \times_S \operatorname{Spec} O$) is $E.I$. Then there is a `RelEffCartierDiv f r g`, i.e. a relative effective Cartier divisor of degree $r$ on $\mathcal C \times_S \operatorname{Spec} O$ over $\operatorname{Spec} O$, whose ideal sheaf datum is exactly $J$ and whose pullback along $\psi$ is $E$.
--
--   This is the spreading-out step for relative divisors over a discrete valuation ring: a flat closed subscheme of a proper $O$-scheme whose generic fibre is a relative effective Cartier divisor of degree $r$ is itself one of degree $r$ over $\operatorname{Spec} O$. It is used in the construction of the saturation of a divisor over a discrete valuation ring, via [`AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_and_pullbackAlong_eq_and_saturated_of_isDiscreteValuationRing`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_and_pullbackAlong_eq_and_saturated_of_isDiscreteValuationRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f]
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (g : Spec (CommRingCat.of O) ⟶ S)
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S} (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g = gT)
    {r : ℕ} (E : RelEffCartierDiv f r gT)
    (J : (pullback f g).IdealSheafData) [Flat (J.subschemeι ≫ pullback.snd f g)]
    (hJ : J.comap (mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ) = E.I) :
    ∃ Ebar : RelEffCartierDiv f r g, Ebar.I = J ∧
      Ebar.pullbackAlong (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ = E := by sorry
