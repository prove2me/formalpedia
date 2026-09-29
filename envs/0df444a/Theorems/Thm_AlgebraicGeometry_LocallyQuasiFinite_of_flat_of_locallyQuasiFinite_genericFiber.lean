-- Prove2me | Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_of_flat_of_locallyQuasiFinite_genericFiber
-- name    : AlgebraicGeometry.LocallyQuasiFinite.of_flat_of_locallyQuasiFinite_genericFiber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/14bc0dc1-5420-55ab-a526-bdc56d788f9c
-- title:
--   Flat, locally finite type with quasi-finite generic fibre is locally quasi-finite
-- statement:
--   Let $R$ be a commutative ring which is a Noetherian domain of Krull dimension at most one (`Ring.DimensionLEOne`), let $K$ be a field equipped with an $R$-algebra structure making it the fraction field of $R$, with $R$ and $K$ in the same universe $u$, and let $Y$ be a scheme in that universe. Let $f \colon Y \to \operatorname{Spec} R$ be a morphism of schemes, where $\operatorname{Spec} R$ means the spectrum of $R$ viewed as an object of `CommRingCat`. Assume $f$ is flat and locally of finite type, and assume that the second projection of the pullback of $f$ along the morphism $\operatorname{Spec} K \to \operatorname{Spec} R$ induced by the structure map $R \to K$ — that is, the generic fibre $Y_K = Y \times_{\operatorname{Spec} R} \operatorname{Spec} K \to \operatorname{Spec} K$ — is locally quasi-finite. The conclusion is that $f$ itself is locally quasi-finite. All three morphism-property hypotheses and the conclusion are the Mathlib morphism-property classes `Flat`, `LocallyOfFiniteType` and `LocallyQuasiFinite`, taken as instance arguments.
--
--   This is the standard criterion for checking quasi-finiteness of a flat family over a one-dimensional Noetherian base on the generic fibre alone (EGA IV$_3$ 13.1; cf. Bosch–Lütkebohmert–Raynaud, *Néron Models*, 2.4); flatness is essential, as $\operatorname{Spec} R[x]/(\pi x) \to \operatorname{Spec} R$ shows. It is used in the treatment of Néron models and of relative effective Cartier divisors on modular curves, for instance to verify that multiplication-by-$n$ maps and base changes of identity components are locally quasi-finite.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_LocallyQuasiFinite_of_flat_of_locallyQuasiFinite_genericFiber.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

theorem AlgebraicGeometry.LocallyQuasiFinite.of_flat_of_locallyQuasiFinite_genericFiber
    {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.DimensionLEOne R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) [Flat f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    LocallyQuasiFinite f := by sorry
