-- Prove2me | Theorems.Thm_Algebra_exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed
-- name    : Algebra.exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/d624ade2-4b33-5506-a102-e21624adc795
-- title:
--   A height-one prime containing the different inside a given prime
-- statement:
--   Let $A$ be a Noetherian integrally closed domain with fraction field $K$, let $B$ be an integrally closed domain which is an $A$-algebra, finite and free as an $A$-module, and let $L$ be a field which is a fraction field of $B$ and is also a $K$-algebra and an $A$-algebra, all four structure maps forming compatible scalar towers ($A \to K \to L$ and $A \to B \to L$), with $L/K$ separable. Write $C = \mathrm{traceDual}\,_A^K(1)$ for the $A$-trace dual in $L$ of the unit $B$-submodule $1 \subseteq L$ (the image of $B$), and let $\mathfrak D \subseteq B$ be the preimage under $b \mapsto \mathrm{algebraMap}\,(b)$ of the submodule quotient $1/C = \{x \in L : xC \subseteq 1\}$, i.e. the different ideal of $B$ over $A$. Let $P$ be a prime ideal of $B$ with $\mathfrak D \le P$. Then there is a prime ideal $Q$ of $B$ with $Q \le P$, of Krull height exactly $1$, and with $\mathfrak D \le Q$.
--
--   This is the statement that the different is contained in a height-one prime below any prime containing it, the form of divisoriality needed to reduce unramifiedness questions to codimension one. It is used in the proofs that an algebra unramified at all height-one primes is unramified, and in the comparison of the different with the radical of the ramification locus in characteristic zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsSeparable K L]
    (P : Ideal B) [P.IsPrime]
    (h : ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L)) ≤ P) :
    ∃ Q : Ideal B, Q.IsPrime ∧ Q ≤ P ∧ Q.height = 1 ∧
      ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L)) ≤ Q := by sorry
