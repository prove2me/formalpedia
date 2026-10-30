-- Prove2me | Theorems.Thm_ConsensusHalvingItems_Additive_reachable_invariant
-- name    : ConsensusHalvingItems.Additive.reachable_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:39:44.770675+00:00
-- url     : https://prove2.me/theorems/3cf4a8cc-03e5-499e-a77c-2f75a08f46ec
-- title:
--   Proof of Theorem 2.2: invariant of the loop
-- statement:
--   For every state $(T, x)$ reached by the while loop of the algorithm (started at $x_1 = \dots = x_m = 1/2$, $T = \emptyset$):
--
--   1. $x$ is a consensus halving, and
--   2. every item $j \in T$ is uncut: $x_j \in \{0, 1\}$.
--
--   These are the paper's conclusions "$(x_1, \dots, x_m)$ remains a consensus halving throughout the algorithm" and "every item $j \in T$ is uncut".
--
--   Differences from the source:
--   - reading: real utilities ui(j) (no encoding fixed) → rational values u : Fin n → Fin m → ℚ; reason: an algorithm takes encoded input; reals have no finite encoding (Reading 2)
--   - encoding: the algorithm of Steps 1–4 with free choices (footnote 5's arbitrary non-pivot value, the argmin of Step 3b) → the definitions kernelDir / findSolution / loopStep / halve with the canonical kernel vector and lowest-index tie-break; reason: the paper leaves these choices open; any fixed choice is an instance of its algorithm (Reading 3)
--   - generalization: nonnegative utilities; N = [n], M = [m] for positive n, m → values of any sign; n = 0 and m = 0 allowed; reason: the p. 6 remark extends the algorithm to negative values; the statement specializes to nonnegative values and positive n, m
--   - encoding: partition (M1, M2) of the items M = [m]; agents N = [n] → (x, 1 − x) with x : Fin m → ℚ; 0-based Fin n, Fin m; reason: a two-part partition is determined by its first part; same instances
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, ¶3 and ¶4, p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_Reachable
import Definitions.Def_ConsensusHalvingItems_Additive_IsConsensusHalving

namespace ConsensusHalvingItems.Additive

/-- **Invariant of the loop: a consensus halving with every item of T uncut.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, p. 5, ¶3: "Thus, (x1, . . . , xm) remains a
consensus halving throughout the algorithm." and ¶4: "As a result, every item j ∈ T is uncut."

For every state `(T, x)` reached by the loop of the algorithm, `x` is a consensus halving for
`u` and `x j ∈ {0, 1}` for every `j ∈ T`.

**Formalization Note.** Stated for the states the algorithm constructs (`Reachable`), starting
from `x ≡ 1/2`, `T = ∅`. -/
theorem reachable_invariant {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) (h : Reachable u (T, x)) :
    IsConsensusHalving u x ∧ ∀ j ∈ T, x j = 0 ∨ x j = 1 := by sorry

end ConsensusHalvingItems.Additive
