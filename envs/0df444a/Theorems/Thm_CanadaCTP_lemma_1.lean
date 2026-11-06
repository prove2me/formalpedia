-- Prove2me | Theorems.Thm_CanadaCTP_lemma_1
-- name    : CanadaCTP.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:19:25.644779+00:00
-- url     : https://prove2.me/theorems/0e99ca56-284f-46a5-ad2e-2f1b04159aab
-- title:
--   Lemma 1 — coin strategies suffice for PathOpt
-- statement:
--   Let $X=(X_j)_{j\in[m]}$ be the independent weights of a path with $m\ge0$ edges. For every algorithm $A^*$ for the PathOpt problem there is $\mathrm{coin}\in\mathrm{COIN}$ such that
--   $$
--   \mathrm{arrivalProb}(\mathrm{coin})=\mathrm{arrivalProb}(A^*)\quad\text{and}\quad \mathrm{expCost}(\mathrm{coin})\le\mathrm{expCost}(A^*).
--   $$
--   Here $A^*$ is any randomized adaptive algorithm on the path: it may use memory, walk back and stop.
--
--   So optimal PathOpt algorithms can be searched among coin strategies, which is what PathExplorer does.
--
--   **Formalization Note** The budget $b$ of the printed statement does not occur in its conclusion and is omitted.
--
--   Differences from the source:
--   - encoding: for every algorithm A* … and budget b ≥ 0 → for every policy A on the path instance (b omitted); reason: b does not occur in the conclusion
--   - encoding: an algorithm for the PathOpt problem (randomized) → a randomized stateful policy Policy (pathInst X) Mem of any memory type Mem : Type; reason: this is the class of randomized adaptive algorithms on the path; walking back and stopping are allowed
--   - encoding: probabilities and expected values of the whole (possibly unbounded) run → suprema over the horizon N of the N-step quantities, in ℝ≥0∞; reason: the events are absorbing and the costs non-decreasing in N, so the suprema are the limits, i.e. the same values
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Lemma 1, p.7; proof pp.32–34

import Mathlib
import Definitions.Def_CanadaCTP_PathOpt

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Lemma 1, p.7 (proof pp.32–34): every PathOpt algorithm `A` is matched by a coin
strategy with the same arrival probability and no larger expected cost.

**Formalization Note.** A PathOpt algorithm is any randomized stateful policy on the path
instance (it may walk back and stop). The budget `b` of the printed statement does not occur in
its conclusion and is omitted. -/
theorem lemma_1 {m : ℕ} (X : Fin m → EdgeDist) (Mem : Type) (A : Policy (pathInst X) Mem) :
    ∃ c : Coin X, InCOIN X c ∧
      arrProb (pathInst X) (coinPolicy X c) = arrProb (pathInst X) A ∧
      expCost (pathInst X) (coinPolicy X c) ≤ expCost (pathInst X) A := by sorry

end CanadaCTP
