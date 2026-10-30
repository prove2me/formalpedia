-- Prove2me | Theorems.Thm_DiazModulus_exists_mem_forall_notMem_of_not_subset
-- name    : DiazModulus.exists_mem_forall_notMem_of_not_subset
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:32.555225+00:00
-- url     : https://prove2.me/theorems/a245d794-5d93-4c09-952c-e65ea3045d46
-- title:
--   Over an infinite field $K$, a $K$-subspace of an algebra contained in none of finitely many ideals has an element outside all of them
-- statement:
--   Let $K$ be an infinite field, $S$ a commutative $K$-algebra, $V$ a $K$-subspace of $S$ and $\mathcal{P}$ a finite set of ideals of $S$ (not necessarily prime) such that $V \not\subseteq p$ for every $p \in \mathcal{P}$. Then some $x \in V$ lies in no $p \in \mathcal{P}$.
--
--   **Proof.** For each $p \in \mathcal{P}$, $V \cap p$ is a $K$-subspace of $V$, proper since $V \not\subseteq p$. A vector space over an infinite field is not a finite union of proper subspaces, so some $x \in V$ lies in no $V \cap p$.
--
--   **Novelty.** Classical; routine formalisation. Compare the choice of $P_{k+1}$ in the proof of DALAG Th. 8.4 (pp. 237–238).
-- source:
--   Classical (avoidance over an infinite field). Compare the choice of P_(k+1) in the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 8.4 (§8.2.3, pp. 237–238; Chapter 8 is by D. Roy). C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem exists_mem_forall_notMem_of_not_subset {K S : Type*} [Field K] [CommRing S] [Algebra K S] [Infinite K]
    (V : Submodule K S) (P : Set (Ideal S)) (hP : P.Finite)
    (hV : ∀ p ∈ P, ¬ (V : Set S) ⊆ (p : Set S)) :
    ∃ x ∈ V, ∀ p ∈ P, x ∉ p := by
  sorry

end DiazModulus
