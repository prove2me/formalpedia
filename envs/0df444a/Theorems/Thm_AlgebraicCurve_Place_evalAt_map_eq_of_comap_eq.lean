-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_evalAt_map_eq_of_comap_eq
-- name    : AlgebraicCurve.Place.evalAt_map_eq_of_comap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/c3d541c7-c6ee-5fc1-a6f5-962cd5dfb36e
-- title:
--   Evaluation at a rational place commutes with constant field extension
-- statement:
--   Let $K, F, K', F'$ be fields with $F$ a $K$-algebra and $F'$ a $K'$-algebra. Let $\tau : K \to K'$ and $\varphi : F \to F'$ be ring homomorphisms compatible with the structure maps, in the sense that $\varphi(\mathrm{alg}_{K,F}(c)) = \mathrm{alg}_{K',F'}(\tau c)$ for all $c \in K$. Let $v$ be a place of $F$ over $K$, that is, a valuation subring $\mathcal{O}_v \subseteq F$ which contains the image of $K$, is not all of $F$, and is a principal ideal ring; let $v'$ be such a place of $F'$ over $K'$. Assume that $v'$ lies over $v$ along $\varphi$, i.e. $\varphi^{-1}(\mathcal{O}_{v'}) = \mathcal{O}_v$, and that $v$ is rational, i.e. the map $K \to \mathcal{O}_v/\mathfrak{m}_v$ to the residue field is surjective. Then for every $x \in \mathcal{O}_v$ one has $\mathrm{evalAt}_{v'}(\varphi x) = \tau(\mathrm{evalAt}_v(x))$, where $\mathrm{evalAt}_w(f)$ is defined to be a preimage, under the map from the constant field to the residue field of $w$, of the residue of $f$ when $f$ lies in $\mathcal{O}_w$, and $0$ otherwise. Rationality of $v'$ is not assumed; the conclusion asserts in particular that the residue of $\varphi x$ at $v'$ comes from $K'$.
--
--   This is the compatibility of evaluation at a rational place with extension of the constant field, as in the theory of constant field extensions of algebraic function fields. It is used in the comparison of places under base change and in the estimates for hyperplane sections on modular curves that invoke values of functions at rational places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_evalAt_map_eq_of_comap_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_map_eq_of_comap_eq {K F K' F' : Type*}
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    (τ : K →+* K') (φ : F →+* F') (hφ : ∀ c : K, φ (algebraMap K F c) = algebraMap K' F' (τ c))
    (v : Place K F) (v' : Place K' F') (h : v'.toValuationSubring.comap φ = v.toValuationSubring)
    (hv : v.IsRational) {x : F} (hx : x ∈ v.toValuationSubring) :
    v'.evalAt (φ x) = τ (v.evalAt x) := by sorry
