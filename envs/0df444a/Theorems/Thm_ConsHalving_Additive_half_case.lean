-- Prove2me | Theorems.Thm_ConsHalving_Additive_half_case
-- name    : ConsHalving.Additive.half_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:39.361183+00:00
-- url     : https://prove2.me/theorems/c0d6e900-72e1-4d6b-ae90-c72a6e5f493d
-- title:
--   Proof of Theorem 2.2, p. 5 — if n ≥ m, halving every item is a consensus halving with m = min{n, m} cuts
-- statement:
--   Let $n$ agents have additive utilities $u_i(j)$ over $m$ items, and suppose $n\ge m$. Then the partition that divides every item in half, $x_j=\tfrac12$ for all $j$, is a consensus halving, and it cuts exactly
--   $$m=\min\{n,m\}$$
--   items.
--
--   This disposes of the case $n\ge m$ of Theorem 2.2; the algorithm handles $n\le m$.
--
--   **Formalization Note** The utilities are arbitrary reals (the nonnegativity of §2 is not needed).
-- source:
--   Goldberg et al., Consensus Halving for Sets of Items, arXiv:2007.06754v1, p. 5, proof of Theorem 2.2, first sentence

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

namespace ConsHalving.Additive

theorem half_case {n m : ℕ} (u : Fin n → Fin m → ℝ) (hnm : m ≤ n) :
    IsConsensusHalving u (fun _ => 1 / 2) ∧
      numCuts (fun _ : Fin m => (1 / 2 : ℝ)) = min n m := by sorry

end ConsHalving.Additive
