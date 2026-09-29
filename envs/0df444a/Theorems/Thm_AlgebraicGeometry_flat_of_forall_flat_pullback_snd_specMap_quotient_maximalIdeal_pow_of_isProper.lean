-- Prove2me | Theorems.Thm_AlgebraicGeometry_flat_of_forall_flat_pullback_snd_specMap_quotient_maximalIdeal_pow_of_isProper
-- name    : AlgebraicGeometry.flat_of_forall_flat_pullback_snd_specMap_quotient_maximalIdeal_pow_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/da533c61-b129-5bcf-b9ef-e7acf2193b83
-- title:
--   Flatness of a proper morphism from flat 𝔪-adic truncations
-- statement:
--   Let $R$ be a commutative ring in the universe $u$ that is noetherian and local, with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal R`, let $Z$ be a scheme in the universe $u$, and let $f : Z \to \operatorname{Spec} R$ be a morphism of schemes that is proper (`IsProper f`). Assume that for every natural number $n$ the second projection out of the fibre product of $f$ with the morphism $\operatorname{Spec}(R/\mathfrak m^{\,n+1}) \to \operatorname{Spec} R$ induced by the quotient map $R \to R/\mathfrak m^{\,n+1}$, that is the morphism $Z \times_{\operatorname{Spec} R} \operatorname{Spec}(R/\mathfrak m^{\,n+1}) \to \operatorname{Spec}(R/\mathfrak m^{\,n+1})$, is flat. Then $f$ itself is flat. Note that the hypothesis is indexed by the exponents $n+1 \ge 1$, so no condition is imposed by the exponent $0$.
--
--   This is the scheme-theoretic form of the local criterion of flatness over a noetherian local base: flatness of a proper morphism is detected on the $\mathfrak m$-adic truncations of the base. It is used in the construction of fake elliptic curves in the Čerednik–Drinfeld part of the development, where a family is produced over a noetherian local ring by successive approximation and must be shown flat.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_flat_of_forall_flat_pullback_snd_specMap_quotient_maximalIdeal_pow_of_isProper.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.flat_of_forall_flat_pullback_snd_specMap_quotient_maximalIdeal_pow_of_isProper
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hflat : ∀ n : ℕ,
      Flat (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))))) :
    Flat f := by sorry
