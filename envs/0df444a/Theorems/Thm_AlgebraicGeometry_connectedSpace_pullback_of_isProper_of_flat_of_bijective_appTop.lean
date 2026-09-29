-- Prove2me | Theorems.Thm_AlgebraicGeometry_connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop
-- name    : AlgebraicGeometry.connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/13147689-a7b6-59d6-ba2b-143851ea3ab0
-- title:
--   Geometric fibres of a proper flat scheme with Γ=ℤ[1/M] are connected
-- statement:
--   Let $M$ be a nonzero natural number and write $\mathbb{Z}[1/M]$ for the localisation `Localization.Away ((M : ℕ) : ℤ)` of $\mathbb{Z}$ away from $M$. Let $X$ be a scheme (in universe $0$) and let $\pi_X : X \to \operatorname{Spec}\mathbb{Z}[1/M]$ be a morphism that is proper and flat. Assume that the ring map induced by $\pi_X$ on global sections over the whole space, $\pi_X$`.appTop` $: \mathbb{Z}[1/M] \to \Gamma(X,\mathcal{O}_X)$, is bijective as a function (so $X$ is "Stein" over its base: its ring of global functions is exactly $\mathbb{Z}[1/M]$). Let $k$ be an algebraically closed field (a type in universe $0$) and let $s : \operatorname{Spec} k \to \operatorname{Spec}\mathbb{Z}[1/M]$ be an arbitrary morphism of schemes, i.e. an arbitrary $\mathbb{Z}[1/M]$-point of $\operatorname{Spec} k$. The conclusion is that the underlying topological space of the fibre product $X \times_{\operatorname{Spec}\mathbb{Z}[1/M]} \operatorname{Spec} k$, formed as `pullback πX s`, is a connected space; since `ConnectedSpace` includes nonemptiness, the geometric fibre is in particular nonempty.
--
--   This is the geometric form of Zariski's connectedness theorem for a proper flat scheme over $\mathbb{Z}[1/M]$ whose ring of global functions is the base ring, with no reducedness hypothesis imposed; the argument passes through a noetherian local flat $\mathbb{Z}[1/M]$-algebra with residue field $k$ (Witt vectors in positive residue characteristic), using that global sections commute with flat base change over an affine base and the preconnectedness of the closed fibre of a proper morphism with bijective map on global sections. It is used in the proof of [`AlgebraicGeometry.isIntegral_and_isIntegral_pullback_of_smooth_isProper_of_isIntegral_pullback`](thm.html#AlgebraicGeometry.isIntegral_and_isIntegral_pullback_of_smooth_isProper_of_isIntegral_pullback), in the geometric input to the study of the integral models occurring later in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

theorem AlgebraicGeometry.connectedSpace_pullback_of_isProper_of_flat_of_bijective_appTop
    (M : ℕ) [NeZero M]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))) [IsProper πX] [Flat πX]
    (hΓ : Function.Bijective πX.appTop)
    (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))) :
    ConnectedSpace ↥(pullback πX s) := by sorry
