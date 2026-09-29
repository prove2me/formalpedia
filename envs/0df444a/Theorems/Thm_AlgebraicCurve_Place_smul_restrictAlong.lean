-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_smul_restrictAlong
-- name    : AlgebraicCurve.Place.smul_restrictAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/2025e48a-ae45-5d0a-a663-37452f35952d
-- title:
--   Restriction of places along a commuting square
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ $K$-algebras. Let $\alpha,\beta : F \to F'$ be $K$-algebra homomorphisms, each assumed integral as a ring homomorphism (hypotheses $h\alpha$, $h\beta$), let $\sigma$ be a $K$-algebra automorphism of $F'$ and $\tau$ a $K$-algebra automorphism of $F$, and assume the square commutes pointwise: $\alpha(\tau x) = \sigma(\beta x)$ for all $x \in F$. Here a `Place K F` is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and whose underlying ring is a principal ideal ring; for an integral $K$-algebra map $\varphi$, `Place.restrictAlong` sends a place $w$ of $F'$ to the place of $F$ whose valuation subring is the preimage $\{f \in F : \varphi f \in w\}$, and automorphisms act on places by pointwise translation of the valuation subring. The assertion is that for every place $W$ of $F'$ over $K$, the restriction along $\alpha$ of $\sigma \bullet W$ coincides, as a place of $F$ over $K$, with $\tau \bullet (W.\mathrm{restrictAlong}\ \beta)$.
--
--   This is the basic functoriality used to transport places through a commuting square of function-field maps, e.g. when comparing the two degeneracy maps of a modular correspondence twisted by a Galois or Atkin–Lehner type automorphism. It is invoked repeatedly in the analysis of place specialisations on modular curves, where prolongations of places along one projection must be matched with translates of prolongations along the other.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_smul_restrictAlong.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.smul_restrictAlong {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (α β : F →ₐ[K] F') (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral) (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x)) (W : Place K F') : (σ • W).restrictAlong α hα = τ • W.restrictAlong β hβ := by sorry
