-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_smul
-- name    : AlgebraicCurve.Place.ramificationIndexAlong_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/e267dcfc-38ca-55fd-9362-eb1cc4d3e7aa
-- title:
--   Ramification indices along a commuting square of places
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ given as $K$-algebras, let $\alpha, \beta : F \to F'$ be two $K$-algebra homomorphisms, let $\sigma$ be a $K$-algebra automorphism of $F'$ and $\tau$ a $K$-algebra automorphism of $F$, and assume the square commutes in the form $\alpha(\tau x) = \sigma(\beta x)$ for every $x \in F$. Let $W$ be a place of $F'$ over $K$, that is, a valuation subring of $F'$ containing the image of $K$, different from $F'$ itself, and a principal ideal ring. Write $\sigma \cdot W$ for the image of $W$ under the pointwise action of $\sigma$, so that $x$ lies in $\sigma \cdot W$ exactly when $\sigma^{-1}x$ lies in $W$. The conclusion is the equality of the two ramification indices along the given homomorphisms: the infimum of the set of integers $n > 0$ for which there is a nonzero $f \in F$ with $\operatorname{ord}_{\sigma \cdot W}(\alpha f) = n$ equals the infimum of the set of integers $n > 0$ for which there is a nonzero $f \in F$ with $\operatorname{ord}_W(\beta f) = n$. No integrality hypothesis on $\alpha$ or $\beta$ is imposed.
--
--   This is the equivariance statement $e(\sigma \cdot W/\alpha) = e(W/\beta)$ for ramification indices of places under a commuting square of maps of function fields, stated for the project's notion of place as a principal valuation subring over the base field. It is used in the analysis of places of modular curves and their specializations, in particular in the bookkeeping of ramification indices along Hecke correspondences and in the computations distinguishing the cuspidal from the non-cuspidal contributions in a fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ramificationIndexAlong_smul.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ramificationIndexAlong_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (α β : F →ₐ[K] F') (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x)) (W : Place K F') : (σ • W).ramificationIndexAlong α = W.ramificationIndexAlong β := by sorry
