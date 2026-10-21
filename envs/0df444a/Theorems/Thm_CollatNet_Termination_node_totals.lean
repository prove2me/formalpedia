-- Prove2me | Theorems.Thm_CollatNet_Termination_node_totals
-- name    : CollatNet.Termination.node_totals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:01.921117+00:00
-- url     : https://prove2.me/theorems/c91ea847-21c3-4b51-b089-f7c17ec0aa40
-- title:
--   Proof of Proposition 2.1, p. 35 (PDF 36) — Round 2 node totals equal remaining obligations or available collateral and receipts
-- statement:
--   Let a network satisfy the standing assumptions, and let $p^{(1)}$ and $p^{(2)}$ be clearing payments of the two-round freed-collateral model of §2.3. In Round 2, the remaining obligation is $\bar p^{(2)}_{ij}=\bar p_{ij}-p^{(1)}_{ij}$ and $r_i$ is collateral returned after Round 1. For every node $i$, the paper's node-total identity reads
--   $$
--   p^{(2)}_i=\bar p^{(2)}_i\wedge\left(r_i+\sum_{k\ne i}p^{(2)}_{ki}\right),\qquad p^{(2)}_i=\sum_j p^{(2)}_{ij},\quad\bar p^{(2)}_i=\sum_j\bar p^{(2)}_{ij}.
--   $$
--   The identity describes the pro rata Round 2 clearing equation (14): each node pays the lesser of what remains due and the resources made available in that round.
--
--   **Formalization Note.** Sums over all nodes equal the paper's sums over $k\ne i$ under the zero-diagonal standing assumptions.
-- source:
--   Ghamami, Glasserman & Young, Collateralized networks, accepted manuscript (Management Science 68(3), 2022; LSE Research Online 107496, version November 2020), proof of Proposition 2.1 (A.2), p. 35 (PDF 36), (11)–(14)

import Mathlib
import Definitions.Def_CollatNet_Termination_Model

namespace CollatNet.Termination

/-- Proof of Proposition 2.1, p. 35: in the freed-collateral Round 2 of §2.3, a node's total
payment is the lesser of its remaining obligation and its returned collateral plus receipts. -/
theorem node_totals {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Network ι)
    (hX : X.Standing) (p1 p2 : ι → ι → ℝ)
    (hp1 : Clears1 X p1) (hp2 : ClearsBase2 X p1 p2) (i : ι) :
    ∑ j, p2 i j =
      min (∑ j, baseObl2 X p1 i j) (returned2 X p1 i + ∑ k, p2 k i) := by sorry

end CollatNet.Termination
