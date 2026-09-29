-- Prove2me | Theorems.Thm_AlgebraicGeometry_geometricallyReduced_pullback_snd_specMap_of_isReduced_of_charZero
-- name    : AlgebraicGeometry.geometricallyReduced_pullback_snd_specMap_of_isReduced_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/925da13f-b8fe-561a-a541-acd2172f5433
-- title:
--   Generic fibre of a reduced scheme over a characteristic-zero domain
-- statement:
--   Let $\mathcal{O}_0$ be a commutative ring which is an integral domain of characteristic zero, and let $K_0$ be a field equipped with an $\mathcal{O}_0$-algebra structure making it a fraction ring of $\mathcal{O}_0$ (i.e. the localisation of $\mathcal{O}_0$ at its non-zero-divisors). Let $\mathcal{X}_0$ be a scheme and $f_0 \colon \mathcal{X}_0 \to \operatorname{Spec} \mathcal{O}_0$ a morphism of schemes, and assume that $\mathcal{X}_0$ is reduced and that $f_0$ is locally of finite type. Form the fibre product of $f_0$ with the morphism $\operatorname{Spec} K_0 \to \operatorname{Spec} \mathcal{O}_0$ induced by the structure map $\mathcal{O}_0 \to K_0$. The conclusion is that the second projection
--   $$\mathcal{X}_0 \times_{\operatorname{Spec} \mathcal{O}_0} \operatorname{Spec} K_0 \longrightarrow \operatorname{Spec} K_0$$
--   is geometrically reduced, i.e. satisfies `GeometricallyReduced`: the generic fibre of $f_0$ remains reduced after base change along any field extension of $K_0$.
--
--   This is the standard statement that the generic fibre of a reduced scheme locally of finite type over a characteristic-zero domain is geometrically reduced. It is used to supply the reducedness half of the geometric properties of a curve model in the Čerednik–Drinfel'd setting, and is the engine of the corresponding statement over a base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_geometricallyReduced_pullback_snd_specMap_of_isReduced_of_charZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.geometricallyReduced_pullback_snd_specMap_of_isReduced_of_charZero
    (𝒪₀ : Type u) [CommRing 𝒪₀] [IsDomain 𝒪₀] [CharZero 𝒪₀]
    (K₀ : Type u) [Field K₀] [Algebra 𝒪₀ K₀] [IsFractionRing 𝒪₀ K₀]
    (𝒳₀ : Scheme.{u}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀)) [IsReduced 𝒳₀] [LocallyOfFiniteType f₀] :
    GeometricallyReduced (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap 𝒪₀ K₀)))) := by sorry
