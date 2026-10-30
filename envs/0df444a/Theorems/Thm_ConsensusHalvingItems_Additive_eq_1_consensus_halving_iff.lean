-- Prove2me | Theorems.Thm_ConsensusHalvingItems_Additive_eq_1_consensus_halving_iff
-- name    : ConsensusHalvingItems.Additive.eq_1_consensus_halving_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:35:42.635724+00:00
-- url     : https://prove2.me/theorems/eeb2d239-a69a-4682-aaed-2073a6761962
-- title:
--   Equation (1): consensus halving under additivity
-- statement:
--   Let $n$ agents have additive utilities $u_i(j)$ over $m$ items, and let $x$ be a fractional set of items ($0 \le x_j \le 1$). Then the partition $(x, 1 - x)$ is a consensus halving if and only if
--
--   $$
--   \sum_{j \in M} x_j \cdot u_i(j) = \frac{1}{2} \sum_{j \in M} u_i(j) \qquad \forall i \in N. \tag{1}
--   $$
--
--   Equation (1) turns the consensus-halving condition into a system of linear equations in the fractions $x_j$, which is what the algorithm of Theorem 2.2 manipulates.
--
--   Differences from the source:
--   - reading: real utilities ui(j) (no encoding fixed) → rational values u : Fin n → Fin m → ℚ; reason: an algorithm takes encoded input; reals have no finite encoding (Reading 2)
--   - generalization: nonnegative utilities; N = [n], M = [m] for positive n, m → values of any sign; n = 0 and m = 0 allowed; reason: the p. 6 remark extends the algorithm to negative values; the statement specializes to nonnegative values and positive n, m
--   - encoding: partition (M1, M2) of the items M = [m]; agents N = [n] → (x, 1 − x) with x : Fin m → ℚ; 0-based Fin n, Fin m; reason: a two-part partition is determined by its first part; same instances
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, eq. (1), p. 4

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_IsConsensusHalving

namespace ConsensusHalvingItems.Additive

/-- **Equation (1): the consensus-halving condition under additivity.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, eq. (1), p. 4: "Observe that under additivity, M′ forms one part of a
consensus halving exactly when Σ_{j∈M} xj · ui(j) = (1/2) Σ_{j∈M} ui(j) ∀i ∈ N."

For every fractional set `x` (all `x j ∈ [0, 1]`), the partition `(x, 1 - x)` is a consensus
halving for the additive utilities `u` if and only if `∑_j x j * u i j = 1/2 * ∑_j u i j` for
every agent `i`.

**Formalization Note.** Agents `Fin n`, items `Fin m` (0-based); rational values of any sign
(p. 6 remark); `n = 0` and `m = 0` allowed. -/
theorem eq_1_consensus_halving_iff {n m : ℕ} (u : Fin n → Fin m → ℚ) (x : Fin m → ℚ)
    (hx : IsFractionalSet x) :
    IsConsensusHalving u x ↔ ∀ i, ∑ j, x j * u i j = 1 / 2 * ∑ j, u i j := by sorry

end ConsensusHalvingItems.Additive
