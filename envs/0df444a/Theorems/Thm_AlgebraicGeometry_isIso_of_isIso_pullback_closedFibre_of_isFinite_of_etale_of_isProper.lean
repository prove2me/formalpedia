-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper
-- name    : AlgebraicGeometry.isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/17c4f68a-cc02-5fb9-91c6-810d688c66a6
-- title:
--   Finite étale over proper base: isomorphism from closed fibre
-- statement:
--   Let $R$ be a commutative ring that is local, with residue field $k = R/\mathfrak{m}$ and residue map $\mathrm{IsLocalRing.residue}\,R \colon R \to k$. Let $X$ and $U$ be schemes, let $f \colon X \to \operatorname{Spec} R$ be a proper morphism, and let $\pi \colon U \to X$ be a morphism that is finite and étale. Write $\iota =$ `pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))` for the first projection of the fibre product of $f$ with $\operatorname{Spec} k \to \operatorname{Spec} R$, that is, the canonical morphism from the closed fibre $X_k = X \times_{\operatorname{Spec} R} \operatorname{Spec} k$ to $X$. The hypothesis is that the second projection `pullback.snd π ι` of the fibre product of $\pi$ and $\iota$, namely the base change $\pi_k \colon U \times_X X_k \to X_k$ of $\pi$ along $\iota$, is an isomorphism. The conclusion is that $\pi$ itself is an isomorphism of schemes.
--
--   This is the standard rigidity statement that a finite étale cover of a proper scheme over a local ring is trivial as soon as it is trivial over the closed fibre. It is used in the construction of a section of a finite étale morphism over a proper scheme with Henselian Noetherian local base, in [`AlgebraicGeometry.exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing`](thm.html#AlgebraicGeometry.exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X U : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (π : U ⟶ X) [IsFinite π] [AlgebraicGeometry.Etale π]
    (hk : IsIso (pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))) :
    IsIso π := by sorry
