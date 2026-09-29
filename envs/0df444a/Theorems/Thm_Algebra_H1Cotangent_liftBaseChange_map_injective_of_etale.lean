-- Prove2me | Theorems.Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale
-- name    : Algebra.H1Cotangent.liftBaseChange_map_injective_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/7fb88aa3-c0c0-5efd-b82c-1f04f0d74ef9
-- title:
--   Injectivity of the base-changed H¹-cotangent map for étale extensions
-- statement:
--   Let $R$, $D$ and $T$ be commutative rings in a single universe, with $D$ an $R$-algebra, $T$ a $D$-algebra and an $R$-algebra, the three structures forming a scalar tower $R \to D \to T$, and assume $T$ is étale over $D$. Consider the map on first cotangent cohomology $\mathrm{H}^1(L_{D/R}) \to \mathrm{H}^1(L_{T/R})$ induced by the square consisting of the identity of $R$ and the algebra map $D \to T$, namely `Algebra.H1Cotangent.map R R D T`; since the target is a $T$-module, this $D$-linear map extends by base change to a $T$-linear map $T \otimes_D \mathrm{H}^1(L_{D/R}) \to \mathrm{H}^1(L_{T/R})$. The assertion is that this base-changed map is injective as a function.
--
--   This is the étale case of the left exactness of the Jacobi–Zariski sequence attached to $R \to D \to T$: the natural map $T \otimes_D \mathrm{H}^1(L_{D/R}) \to \mathrm{H}^1(L_{T/R})$ is injective when $T/D$ is étale. It is used as the local input for the corresponding statement with $T$ smooth over $D$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Algebra.H1Cotangent.liftBaseChange_map_injective_of_etale (R D T : Type u)
    [CommRing R] [CommRing D] [CommRing T] [Algebra R D] [Algebra D T] [Algebra R T] [IsScalarTower R D T]
    [Algebra.Etale D T] :
    Function.Injective ((Algebra.H1Cotangent.map R R D T).liftBaseChange T) := by sorry
