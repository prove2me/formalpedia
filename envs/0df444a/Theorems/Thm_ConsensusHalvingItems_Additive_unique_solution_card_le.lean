-- Prove2me | Theorems.Thm_ConsensusHalvingItems_Additive_unique_solution_card_le
-- name    : ConsensusHalvingItems.Additive.unique_solution_card_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:40:00.564624+00:00
-- url     : https://prove2.me/theorems/a701782e-db3e-4682-bf8f-5c156abeff3b
-- title:
--   Proof of Theorem 2.2: a unique solution needs at least $m$ equations
-- statement:
--   Let $A$ be an $r \times m$ matrix over a field $K$ and $b \in K^r$. If the linear system $A y = b$ in $m$ unknowns has a unique solution, then
--
--   $$
--   m \le r ,
--   $$
--
--   that is, the number of equations is at least the number of unknowns. The proof of Theorem 2.2 applies this to the system $S \cup T$ at the end of the algorithm.
--
--   Differences from the source:
--   - generalization: linear equations over the field of the utilities (real numbers) → matrix equations A y = b over an arbitrary field K; reason: the statement specializes to real (and rational) systems
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, ¶5, p. 5

import Mathlib

namespace ConsensusHalvingItems.Additive

/-- **A unique solution needs at least as many equations as unknowns.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, ¶5, p. 5: "Recall that a system of linear
equations with m variables can only have a unique solution when the number of constraints is at
least m."

Let `K` be a field, `A` an `r × m` matrix over `K` and `b ∈ K^r`. If the system `A y = b` has
a solution `y₀` and every solution equals `y₀`, then `m ≤ r`.

**Formalization Note.** Stated over an arbitrary field; the paper uses it over the field of the
utilities. -/
theorem unique_solution_card_le {K : Type*} [Field K] {r m : ℕ} (A : Matrix (Fin r) (Fin m) K)
    (b : Fin r → K) (y₀ : Fin m → K) (hy₀ : A.mulVec y₀ = b)
    (huniq : ∀ y, A.mulVec y = b → y = y₀) : m ≤ r := by sorry

end ConsensusHalvingItems.Additive
