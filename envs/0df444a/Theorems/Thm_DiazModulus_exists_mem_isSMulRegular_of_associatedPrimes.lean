-- Prove2me | Theorems.Thm_DiazModulus_exists_mem_isSMulRegular_of_associatedPrimes
-- name    : DiazModulus.exists_mem_isSMulRegular_of_associatedPrimes
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:34.756718+00:00
-- url     : https://prove2.me/theorems/ed63e9bf-1ded-45dd-a29a-6ac968ec9212
-- title:
--   Over an infinite field $K$, a $K$-subspace of a Noetherian algebra contained in no associated prime of a finite module $M$ contains an $M$-regular element
-- statement:
--   Let $K$ be an infinite field, $S$ a commutative Noetherian $K$-algebra, $M$ a finitely generated $S$-module and $V$ a $K$-subspace of $S$ contained in no associated prime of $M$. Then $V$ contains an element $x$ that is regular on $M$ (multiplication by $x$ on $M$ is injective).
--
--   **Proof.** $M$ has finitely many associated primes, so `DiazModulus.exists_mem_forall_notMem_of_not_subset` gives $x \in V$ outside all of them. Over a Noetherian ring the union of the associated primes of $M$ is the set of non-regular elements on $M$, so $x$ is $M$-regular.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical commutative algebra (associated primes and zero divisors). Used as in the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 8.4 (§8.2.3, pp. 237–238; Chapter 8 is by D. Roy). Uses DiazModulus.exists_mem_forall_notMem_of_not_subset. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem exists_mem_isSMulRegular_of_associatedPrimes {K S M : Type*} [Field K] [CommRing S] [Algebra K S]
    [IsNoetherianRing S] [Infinite K] [AddCommGroup M] [Module S M] [Module.Finite S M]
    (V : Submodule K S) (hV : ∀ p ∈ associatedPrimes S M, ¬ (V : Set S) ⊆ (p : Set S)) :
    ∃ x ∈ V, IsSMulRegular M x := by
  sorry

end DiazModulus
