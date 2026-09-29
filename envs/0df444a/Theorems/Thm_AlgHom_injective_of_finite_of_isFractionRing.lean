-- Prove2me | Theorems.Thm_AlgHom_injective_of_finite_of_isFractionRing
-- name    : AlgHom.injective_of_finite_of_isFractionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/655b950c-addf-5336-886e-f6c8b30e99b2
-- title:
--   Finite k-algebra maps between domains with common fraction field are injective
-- statement:
--   Let $k$ be a field and let $A$ and $B$ be commutative rings that are integral domains and $k$-algebras of finite type (`Algebra.FiniteType k A`, `Algebra.FiniteType k B`). Let $K$ be a field which is a $k$-algebra and which is simultaneously a fraction field of $A$ and of $B$: it carries $A$-algebra and $B$-algebra structures with `IsFractionRing A K` and `IsFractionRing B K`, both compatible with the $k$-algebra structures in the sense of the scalar-tower conditions `IsScalarTower k A K` and `IsScalarTower k B K`. No compatibility is demanded between the two embeddings $A \hookrightarrow K$ and $B \hookrightarrow K$ and the map below; all four types live in one universe. Then for every $k$-algebra homomorphism $\varphi \colon A \to B$ whose underlying ring homomorphism is finite, i.e. makes $B$ a finitely generated module over $A$ via $\varphi$ (`φ.toRingHom.Finite`), the map $\varphi$ is injective as a function, that is, $\ker \varphi = 0$.
--
--   This is the commutative-algebra form of the statement that a finite morphism between affine opens of one integral $k$-scheme of finite type is dominant, so that in particular a finite self-map of a variety is surjective. It is used in the computation of the Krull dimension of local rings under a finite endomorphism, [`AlgebraicGeometry.ringKrullDim_stalk_eq_of_isFinite_endomorphism`](thm.html#AlgebraicGeometry.ringKrullDim_stalk_eq_of_isFinite_endomorphism).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_injective_of_finite_of_isFractionRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem AlgHom.injective_of_finite_of_isFractionRing {k A B K : Type u} [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Field K] [Algebra k K] [Algebra A K] [IsFractionRing A K] [IsScalarTower k A K]
    [Algebra B K] [IsFractionRing B K] [IsScalarTower k B K]
    (φ : A →ₐ[k] B) (hφ : φ.toRingHom.Finite) : Function.Injective φ := by sorry
