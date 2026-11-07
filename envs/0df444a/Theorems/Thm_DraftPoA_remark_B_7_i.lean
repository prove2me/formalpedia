-- Prove2me | Theorems.Thm_DraftPoA_remark_B_7_i
-- name    : DraftPoA.remark_B_7_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:18.484305+00:00
-- url     : https://prove2.me/theorems/fbe1bc8d-9d75-40f7-8394-b538e5544123
-- title:
--   Remark B.7 (i): with continuous bids every completion is a pure Nash equilibrium
-- statement:
--   Let $N\ge4$ and $d\ge0$ dummy items. With $\delta=0$ (every bid in $[0,1]$), the profile has completions, and every completion (arbitrary legal actions of $A$ at damaged states with $F=\emptyset$, $S\ne\emptyset$) is a pure Nash equilibrium.
--
--   So the lower bound for Nash equilibria also holds with continuous bids.
--
--   Differences from the source:
--   - generalization: the instance with m(N) items → every number d of dummy items; reason: needed for every number of items; d = 0 is the source's case
--   - encoding: the profile, completed arbitrarily → existence of a completion, and every completion is a pure Nash equilibrium; reason: existence keeps the universal statement from being vacuous
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), Remark B.7 (i), p.23 (PDF 24)

import Mathlib
import Definitions.Def_DraftPoA_Auction
import Definitions.Def_DraftPoA_Equilibria
import Definitions.Def_DraftPoA_BadInstance

namespace DraftPoA

/-- Remark B.7 (i) (Continuous bids), App. B, p.23 (PDF 24) (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

For `N ≥ 4` and any number `d` of dummy items, with `δ = 0` (every bid in `[0, 1]`) the profile has
completions, and every completion (arbitrary legal actions of `A` at damaged states with `F = ∅`,
`S ≠ ∅`) is a pure Nash equilibrium. -/
theorem remark_B_7_i (N : ℕ) (hN : 4 ≤ N) (d : ℕ) :
    (∃ b : Fin (nBid N) → Strategy (nBid N) (mOf N + d) 0 1, IsCompletion N d b) ∧
    ∀ b : Fin (nBid N) → Strategy (nBid N) (mOf N + d) 0 1, IsCompletion N d b →
      IsPureNash (prioBad N) (vBad N d) b := by sorry

end DraftPoA
