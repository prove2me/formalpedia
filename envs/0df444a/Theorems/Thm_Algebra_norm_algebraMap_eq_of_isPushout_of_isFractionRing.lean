-- Prove2me | Theorems.Thm_Algebra_norm_algebraMap_eq_of_isPushout_of_isFractionRing
-- name    : Algebra.norm_algebraMap_eq_of_isPushout_of_isFractionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/db9f1c1f-42b7-59ab-aaa8-3ec4f04cf063
-- title:
--   Norms commute with base change, read in fraction fields
-- statement:
--   Let $A$, $B$, $A'$, $B'$ be integral domains in a common universe, with algebra structures $A \to B$, $A \to A'$, $B \to B'$, $A' \to B'$ and $A \to B'$ making $A \to B \to B'$ and $A \to A' \to B'$ scalar towers, and assume the square is a pushout of commutative algebras in the sense of `Algebra.IsPushout A B A' B'`, i.e. the induced $A'$-algebra map $A' \otimes_A B \to B'$ is bijective; assume further that $B$ is a finite $A$-module and that both $A \to B$ and $A' \to B'$ are injective. Let $K$, $L$, $K'$, $L'$ be fields that are fraction fields of $A$, $B$, $A'$, $B'$ respectively, with $K \to L$ and $K' \to L'$ and the scalar towers $A \to K \to L$, $A \to B \to L$, $A' \to K' \to L'$, $A' \to B' \to L'$. Let $\varphi \colon K \to K'$ be a ring homomorphism with $\varphi \circ (A \to K) = (A' \to K') \circ (A \to A')$. Then for every $b \in B$, $\varphi\bigl(N_{L/K}(b)\bigr) = N_{L'/K'}(b')$, where $b'$ is the image of $b$ in $B' \subseteq L'$.
--
--   This is the compatibility of the field norm of a finite extension of domains with base change of the base ring, expressed on the level of fraction fields; the proof cites only the fact that the norm of $1 \otimes x$ over a base change $K'$ of $K$ is the image of the norm of $x$. It is used in the scheme-theoretic statement [`AlgebraicGeometry.Scheme.exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed`](thm.html#AlgebraicGeometry.Scheme.exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed) about norms of sections along a finite morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_norm_algebraMap_eq_of_isPushout_of_isFractionRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.norm_algebraMap_eq_of_isPushout_of_isFractionRing
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsDomain A] [IsDomain B] [IsDomain A'] [IsDomain B']
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [Algebra.IsPushout A B A' B']
    [Module.Finite A B] (hAB : Function.Injective (algebraMap A B)) (hA'B' : Function.Injective (algebraMap A' B'))
    (K L K' L' : Type u) [Field K] [Field L] [Field K'] [Field L']
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra A' K'] [IsFractionRing A' K'] [Algebra B' L'] [IsFractionRing B' L']
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L'] [IsScalarTower A' B' L']
    (φ : K →+* K') (hφ : φ.comp (algebraMap A K) = (algebraMap A' K').comp (algebraMap A A'))
    (b : B) :
    φ (Algebra.norm K (algebraMap B L b)) = Algebra.norm K' (algebraMap B' L' (algebraMap B B' b)) := by sorry
