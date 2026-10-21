-- Prove2me | Theorems.Thm_CollatNet_Termination_netWorth_le_payments
-- name    : CollatNet.Termination.netWorth_le_payments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:02.629383+00:00
-- url     : https://prove2.me/theorems/d54088fb-2f97-443b-9824-1452a123a290
-- title:
--   Proof of Proposition 5.2, p. 45 (PDF 46) — a node in D^f − D^(1) pays at least its net worth e_i in rounds ≥ 2
-- statement:
--   Let the network satisfy the standing assumptions, with collateral price $1$, and let $p^{(1)}, \dots, p^{(R)}$ be full-termination clearing payments. If node $i$ survives Round 1 but defaults in a later round, $i \in D^f \setminus D^{(1)}$, then its payments in rounds $2, \dots, R$ are at least its net worth at the end of Round 1:
--   $$
--   \sum_{\ell = 2}^{R} \sum_j p^{(\ell)}_{ij} \;\ge\; e_i = c_i + r_i + \sum_k p^{(1)}_{ki} - \sum_k \bar p_{ik} .
--   $$
--   In the paper's words, if a node paid out less than its net worth, it would not default.
--
--   **Formalization Note.** This step uses the repaired cash recursion of the Model (unsold returned collateral is carried forward as cash; seized collateral is not paid out of cash).
-- source:
--   Ghamami, Glasserman & Young, Collateralized networks, accepted manuscript (Management Science 68(3), 2022; LSE Research Online 107496, version November 2020), proof of Proposition 5.2 (A.9), p. 45 (PDF 46), before (69); e_i is (39), p. 30 (PDF 31)

import Mathlib
import Definitions.Def_CollatNet_Termination_Model

namespace CollatNet.Termination

open Finset

/-- Proof of Proposition 5.2, p. 45: under full termination, a node that survives Round 1 but
defaults in a later round pays out at least its net worth `e_i` (39) over rounds `2, …, R`. -/
theorem netWorth_le_payments {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Network ι)
    (hX : X.Standing) (p : ℕ → ι → ι → ℝ) (hp : ClearsFT X p) :
    ∀ i ∈ Df X p \ D1 X (p 1),
      netWorth X (p 1) i ≤ ∑ l ∈ Icc 2 (numRounds ι), ∑ j, p l i j := by sorry

end CollatNet.Termination
