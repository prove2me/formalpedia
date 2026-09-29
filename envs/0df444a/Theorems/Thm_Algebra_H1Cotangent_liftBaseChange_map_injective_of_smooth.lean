-- Prove2me | Theorems.Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth
-- name    : Algebra.H1Cotangent.liftBaseChange_map_injective_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/96d2a332-c836-57a4-ad46-ed3eeed74b03
-- title:
--   Jacobi–Zariski left exactness over a smooth algebra
-- statement:
--   Let $R$, $S$, $T$ be commutative rings (in a single universe) with algebra structures $R \to S$, $S \to T$ and $R \to T$ forming a scalar tower, and assume $T$ is a smooth $S$-algebra (in Mathlib's sense: formally smooth and of finite presentation over $S$). The functoriality map `Algebra.H1Cotangent.map R R S T` is the $S$-linear map $H^1(L_{S/R}) \to H^1(L_{T/R})$ on first homology of the (naive) cotangent complexes induced by the identity on $R$ and the structure map $S \to T$; since the target is a $T$-module, `liftBaseChange T` turns it into the $T$-linear map $$T \otimes_S H^1(L_{S/R}) \longrightarrow H^1(L_{T/R}).$$ The assertion is that this map is injective. Equivalently, the Jacobi–Zariski sequence for $R \to S \to T$ is left exact at the term $T \otimes_S H^1(L_{S/R})$ when $T$ is smooth over $S$.
--
--   This is the left-hand end of the Jacobi–Zariski exact sequence for a tower $R \to S \to T$ with $T$ smooth over $S$, a refinement of the Mathlib sequence, which starts one term to the right. It is deduced from the corresponding statement for $T$ étale over an intermediate ring, and is used in the proof of [`Algebra.IsSmoothAt.of_isSmoothAt_of_smooth`](thm.html#Algebra.IsSmoothAt.of_isSmoothAt_of_smooth), which descends smoothness at a point along a smooth morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Algebra.H1Cotangent.liftBaseChange_map_injective_of_smooth (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.Smooth S T] :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by sorry
