-- Prove2me | Theorems.Thm_AlgebraicGeometry_isClosedImmersion_of_isFinite_of_forall_isClosedImmersion_pullback_snd_truncation_of_isAdicComplete
-- name    : AlgebraicGeometry.isClosedImmersion_of_isFinite_of_forall_isClosedImmersion_pullback_snd_truncation_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/5c125eea-b3fa-5df8-8bfc-32cdee6f1644
-- title:
--   Closed immersion detected by all I-adic truncations
-- statement:
--   Let $R$ be a noetherian commutative ring and $I \subseteq R$ an ideal such that $R$ is $I$-adically complete. Let $\Gamma, X$ be schemes, let $f : X \to \operatorname{Spec} R$ be a proper morphism and let $h : \Gamma \to X$ be a finite morphism. Let $sR$ be a family of morphisms $sR_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$, for $n \in \mathbb{N}$, subject to the hypothesis $hsR$ that each $sR_n$ is the morphism obtained by applying $\operatorname{Spec}$ to the quotient ring map $R \to R/I^{n+1}$. Write $X_n$ for the chosen pullback of $f$ along $sR_n$, with first projection $\operatorname{pullback.fst} f\,(sR_n) : X_n \to X$. The hypothesis $hn$ is that for every $n$ the base change of $h$ along this projection, namely the second projection $\Gamma \times_X X_n \to X_n$, is a closed immersion. The conclusion is that $h$ itself is a closed immersion.
--
--   This is the formal-completion descent criterion for being a closed immersion: over a complete noetherian base, and for a finite morphism onto a proper scheme, the property of being a closed immersion is detected on the $I$-adic truncations $X_n = X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1})$. It is used in the corresponding criterion for a finite morphism to be an isomorphism, [`AlgebraicGeometry.isIso_of_isFinite_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete`](thm.html#AlgebraicGeometry.isIso_of_isFinite_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isClosedImmersion_of_isFinite_of_forall_isClosedImmersion_pullback_snd_truncation_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isClosedImmersion_of_isFinite_of_forall_isClosedImmersion_pullback_snd_truncation_of_isAdicComplete
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {Γ X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (h : Γ ⟶ X) [IsFinite h]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (hn : ∀ n : ℕ, IsClosedImmersion (Limits.pullback.snd h (Limits.pullback.fst f (sR n)))) :
    IsClosedImmersion h := by sorry
