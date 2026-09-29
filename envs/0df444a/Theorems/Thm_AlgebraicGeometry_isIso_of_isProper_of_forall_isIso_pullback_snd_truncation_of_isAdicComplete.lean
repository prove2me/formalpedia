-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
-- name    : AlgebraicGeometry.isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/1fc4e40b-60fe-5ad6-b68e-ac49e45e4e85
-- title:
--   Proper morphism iso on all I-adic truncations is iso
-- statement:
--   Let $R$ be a commutative noetherian ring, $I \subseteq R$ an ideal, and suppose $R$ is $I$-adically complete. Let $\Gamma$ and $X$ be schemes, let $f : X \to \operatorname{Spec} R$ be proper, and let $h : \Gamma \to X$ be proper. Suppose given, for each $n : \mathbb{N}$, a morphism $s_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$, and assume that each $s_n$ is the morphism induced on spectra by the quotient map $R \to R/I^{n+1}$ (as an algebra map). Write $X_n$ for the chosen pullback of $f$ along $s_n$, with first projection $\mathrm{pr}_1 : X_n \to X$, and form the chosen pullback of $h$ along $\mathrm{pr}_1$, i.e. $\Gamma \times_X X_n$, with second projection to $X_n$. Assume that for every $n$ this second projection $\Gamma \times_X X_n \to X_n$ is an isomorphism. Then $h$ itself is an isomorphism.
--
--   This is the properness version of the statement that a morphism over an $I$-adically complete base which is an isomorphism on every $I$-adic truncation is already an isomorphism (a formal-geometry statement in the circle of EGA III₁ 5.4.1, combined with Zariski's main theorem). It is used in the construction of morphisms to projective space over complete noetherian rings from their truncations, in particular in the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {Γ X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (h : Γ ⟶ X) [IsProper h]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (hn : ∀ n : ℕ, IsIso (Limits.pullback.snd h (Limits.pullback.fst f (sR n)))) :
    IsIso h := by sorry
