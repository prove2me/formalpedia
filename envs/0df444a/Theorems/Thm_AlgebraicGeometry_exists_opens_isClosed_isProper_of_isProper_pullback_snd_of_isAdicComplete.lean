-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete
-- name    : AlgebraicGeometry.exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/ca2d8fb3-b79e-581c-a2b9-42eef07939c3
-- title:
--   Proper clopen neighbourhood of a proper closed fibre
-- statement:
--   Let $A$ be a Noetherian local ring that is complete and separated for the adic topology of its maximal ideal, and let $f \colon X \to \operatorname{Spec} A$ be a morphism of schemes that is separated, locally of finite type and quasi-compact (so $X$ is a separated $A$-scheme of finite type). Let $K$ be a field and let $\iota \colon \operatorname{Spec} K \to \operatorname{Spec} A$ be a closed immersion, and assume that the second projection $\operatorname{pullback.snd} f\ \iota \colon X \times_{\operatorname{Spec} A} \operatorname{Spec} K \to \operatorname{Spec} K$ is proper, i.e. that the fibre of $f$ along $\iota$ is proper over $K$. The assertion is that there exists an open subscheme $U$ of $X$ such that: the underlying set of $U$ is closed in $X$; the composite of the open immersion $U.\iota \colon U \to X$ with $f$ is a proper morphism $U \to \operatorname{Spec} A$; and the set-theoretic image of the first projection $\operatorname{pullback.fst} f\ \iota \colon X \times_{\operatorname{Spec} A} \operatorname{Spec} K \to X$ is contained in $U$. Thus $U$ is an open and closed subscheme of $X$, proper over $A$, containing the fibre along $\iota$.
--
--   This is the case "$Z_0$ the whole closed fibre" of the bijection, over a complete Noetherian base, between open and closed subsets of $X$ proper over $A$ and those of the closed fibre proper over the residue field (EGA III, Proposition 5.5.1 and Corollary 5.5.2), in the form used by Serre and Tate. It is cited by [`AlgebraicGeometry.isProper_of_isProper_pullback_snd_of_geometricallyConnected_of_isLocalRing`](thm.html#AlgebraicGeometry.isProper_of_isProper_pullback_snd_of_geometricallyConnected_of_isLocalRing), which upgrades the conclusion to properness of $f$ itself when the fibre is geometrically connected.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A))
    [IsClosedImmersion ι] [IsProper (pullback.snd f ι)] :
    ∃ U : X.Opens, IsClosed (U : Set X) ∧ IsProper (U.ι ≫ f) ∧
      Set.range (pullback.fst f ι) ⊆ (U : Set X) := by sorry
