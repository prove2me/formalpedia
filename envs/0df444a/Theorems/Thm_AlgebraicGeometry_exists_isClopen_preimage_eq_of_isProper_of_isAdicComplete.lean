-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isClopen_preimage_eq_of_isProper_of_isAdicComplete
-- name    : AlgebraicGeometry.exists_isClopen_preimage_eq_of_isProper_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/de9770db-cda3-52af-8dee-1960a6be1b4c
-- title:
--   Clopen subsets of the closed fibre lift to the scheme
-- statement:
--   Let $A$ be a Noetherian local commutative ring which is complete (in the sense of `IsAdicComplete`) for the adic topology of its maximal ideal, let $P$ be a scheme and let $q \colon P \to \operatorname{Spec} A$ be a proper morphism. Let $K$ be a field and let $\iota \colon \operatorname{Spec} K \to \operatorname{Spec} A$ be a closed immersion. Form the fibre product $P \times_{\operatorname{Spec} A} \operatorname{Spec} K$ in the category of schemes, and let $\operatorname{pullback.fst} q\, \iota$ be its first projection to $P$. Then for every subset $V_0$ of the underlying topological space of this fibre product that is both open and closed, there is a subset $V$ of the underlying space of $P$ which is both open and closed and whose preimage under the first projection is exactly $V_0$. All rings and schemes live in a single universe $u$.
--
--   This is the statement, for a complete Noetherian local base, that every open and closed subset of the closed fibre of a proper scheme is the trace of an open and closed subset of the whole scheme (a topological form of EGA IV, 18.5.19; equivalently, idempotents lift from the closed fibre). It feeds the construction of proper open-and-closed pieces of $P$ used in [`AlgebraicGeometry.exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete`](thm.html#AlgebraicGeometry.exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete), and relies on finiteness of the global sections of a proper morphism over a Noetherian ring, on completeness of finite modules over a complete ring, and on connectedness properties of closed fibres of proper morphisms with bijective global-sections map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isClopen_preimage_eq_of_isProper_of_isAdicComplete.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isClopen_preimage_eq_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A))
    [IsClosedImmersion ι]
    (V₀ : Set ↥(pullback q ι)) (hV₀ : IsClopen V₀) :
    ∃ V : Set P, IsClopen V ∧ pullback.fst q ι ⁻¹' V = V₀ := by sorry
