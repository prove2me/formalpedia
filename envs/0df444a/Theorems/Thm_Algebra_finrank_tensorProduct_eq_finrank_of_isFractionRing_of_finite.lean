-- Prove2me | Theorems.Thm_Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite
-- name    : Algebra.finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/80e04e2a-cbef-52f7-ac9e-646d7acb32ad
-- title:
--   Generic rank equals degree of fraction field extension
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra which is finite as an $A$-module. Let $K$ be a field equipped with an $A$-algebra structure making it a fraction field of $A$ (that is, $K$ is a localisation of $A$ at its non-zero-divisors). Let $F$ be a further field that is a fraction field of $A$ in the same sense, and $F'$ a field that is a fraction field of $B$. Let $\varphi \colon F \to F'$ be a ring homomorphism compatible with the given maps out of $A$, in the sense that for every $a \in A$ the image of $a$ under $A \to B \to F'$ equals $\varphi$ applied to the image of $a$ under $A \to F$. The conclusion is an equality of two ranks: the $K$-dimension of $K \otimes_A B$ equals the $F$-dimension of $F'$, where $F'$ is regarded as an $F$-module through $\varphi$; in classical notation, $\dim_K(K \otimes_A B) = [F' : \varphi(F)]$. Note that $A \to B$ is injective and $B$ is a domain as a consequence of the hypotheses rather than by assumption.
--
--   This is the statement that the generic rank of a module-finite extension $A \to B$, computed by base change to an arbitrary abstract fraction field $K$ of $A$, agrees with the degree of the associated extension of fraction fields; it frees rank computations from any particular choice of fraction field. It is used in the project when comparing ranks over a Dedekind base with degrees of residue or completion field extensions, for instance in the results on inertia and fixed subalgebras, on surjectivity of structure maps for integrally closed rings of equal generic rank, and on ranks after adic completion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {F F' : Type*} [Field F] [Field F'] [Algebra A F] [IsFractionRing A F]
    [Algebra B F'] [IsFractionRing B F'] (φ : F →+* F')
    (hφ : ∀ a : A, algebraMap B F' (algebraMap A B a) = φ (algebraMap A F a)) :
    Module.finrank K (K ⊗[A] B) = @Module.finrank F F' _ _ φ.toAlgebra.toModule := by sorry
