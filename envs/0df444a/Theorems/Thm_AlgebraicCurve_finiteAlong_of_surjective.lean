-- Prove2me | Theorems.Thm_AlgebraicCurve_finiteAlong_of_surjective
-- name    : AlgebraicCurve.finiteAlong_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/37c921ba-5a08-512e-914b-bc710b09079f
-- title:
--   Surjective K-algebra maps of fields are finite
-- statement:
--   Let $K$, $F$, $F'$ be fields, with $F$ and $F'$ equipped with $K$-algebra structures, and let $\varphi \colon F \to F'$ be a homomorphism of $K$-algebras. Assume that $\varphi$ is surjective as a map of underlying sets. Then `FiniteAlong K φ` holds, that is: when $F'$ is regarded as an $F$-algebra via the ring homomorphism underlying $\varphi$ (the algebra structure `algebraAlong φ`, whose structure map is $\varphi$ itself), $F'$ is a finite $F$-module, i.e. finitely generated as a module over $F$ along $\varphi$. Note that the hypothesis is surjectivity of $\varphi$, not a degree or integrality assumption; since a ring homomorphism between fields is automatically injective, such a $\varphi$ is in fact an isomorphism and $F'$ is free of rank one over $F$, but only finiteness is asserted here.
--
--   This is the degenerate case of the finiteness hypothesis used throughout the theory of correspondences between function fields of curves, where a morphism of curves is required to make the target function field a finite extension of the source: an isomorphism of function fields trivially satisfies it. It is invoked to supply the `FiniteAlong` hypothesis for identity-like or isomorphism degeneracy maps, for instance in the compatibility of pushforward and pullback of divisors along a surjective map and in the identities for degeneracy pairs on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finiteAlong_of_surjective.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.finiteAlong_of_surjective {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : Function.Surjective φ) : FiniteAlong K φ := by sorry
