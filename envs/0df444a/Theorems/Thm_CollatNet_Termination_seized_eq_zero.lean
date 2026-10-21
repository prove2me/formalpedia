-- Prove2me | Theorems.Thm_CollatNet_Termination_seized_eq_zero
-- name    : CollatNet.Termination.seized_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:54.720621+00:00
-- url     : https://prove2.me/theorems/c0ee2807-c75b-45c7-8565-9e27cba3ab30
-- title:
--   Proof of Proposition 4.1, p. 43 (PDF 44) — Δ^(m) = 0 for every round m ≥ 2
-- statement:
--   Let the network satisfy the standing assumptions, with collateral price $1$, and let $p^{(1)}, \dots, p^{(R)}$ be full-termination clearing payments. Then for every round $2 \le m \le R$ and all nodes $i, j$, no collateral is seized:
--   $$
--   \Delta^{(m)}_{ij} = 0 .
--   $$
--
--   The reason in the paper is that a node $i \in D^{(m)}$ survived the first $m-1$ rounds, and two survivors owe each other nothing from round 2 on. As a consequence, rounds $m \ge 2$ are Eisenberg–Noe clearing problems with proportions $a^{(m)}_{ij} = \bar p^{(m)}_{ij} / \sum_k \bar p^{(m)}_{ik}$.
-- source:
--   Ghamami, Glasserman & Young, Collateralized networks, accepted manuscript (Management Science 68(3), 2022; LSE Research Online 107496, version November 2020), proof of Proposition 4.1 (A.8), p. 43 (PDF 44)

import Mathlib
import Definitions.Def_CollatNet_Termination_Model

namespace CollatNet.Termination

/-- Proof of Proposition 4.1, p. 43: `Δ^(m)_ij = 0` for every round `m ≥ 2`. -/
theorem seized_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Network ι)
    (hX : X.Standing) (p : ℕ → ι → ι → ℝ) (hp : ClearsFT X p) (k : ℕ)
    (hk : k + 2 ≤ numRounds ι) (i j : ι) :
    seizedAt X (stateFT X p k) (p (k + 2)) i j = 0 := by sorry

end CollatNet.Termination
