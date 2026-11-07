-- Prove2me | Theorems.Thm_DraftPoA_claim_B_6
-- name    : DraftPoA.claim_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:23.524381+00:00
-- url     : https://prove2.me/theorems/cccdb302-d3b2-4fe6-9063-0bb0ffc8ffcd
-- title:
--   Claim B.6 (Completion): the profile is a pure subgame-perfect equilibrium
-- statement:
--   Let $N\ge4$, $d\ge0$ dummy items and $k\ge1$ an integer. On the grid $\delta_N/k$ with cap $\bar M=1$, the profile of §4.2 has a completion (an action of $A$ at every damaged state with $F=\emptyset$, $S\ne\emptyset$) that is a pure subgame-perfect equilibrium.
--
--   This is the equilibrium of Theorem 4.1.
--
--   Differences from the source:
--   - generalization: the profile on the grid δ_N with m(N) items → every d ≥ 0 dummy items and every grid δ_N/k, k ≥ 1; reason: App. B (From N to m) and App. E (every finer grid) extend the claim; k = 1, d = 0 is the source's case
--   - reading: A's damaged-state action optimal by backward induction → ∃ completion that is a pure SPE; reason: the backward-induction completion is such a completion; an SPE makes A's damaged-state action optimal
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), Claim B.6, p.23 (PDF 24); App. B "From N to m", p.21 (PDF 22); App. E "The bid grid", p.32 (PDF 33)

import Mathlib
import Definitions.Def_DraftPoA_Auction
import Definitions.Def_DraftPoA_Equilibria
import Definitions.Def_DraftPoA_BadInstance

namespace DraftPoA

/-- Claim B.6 (Completion), App. B, p.23 (PDF 24), on every grid of Theorem 4.1 (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

For `N ≥ 4`, any number `d` of dummy items and every integer `k ≥ 1`, on the grid `δ_N/k` with
`M̄ = 1` the profile has a completion (an action of `A` at the damaged nodes with `F = ∅`, `S ≠ ∅`)
that is a pure subgame-perfect equilibrium.

**Formalization Note.** The paper completes by a backward-induction best response; the statement
asserts that some completion is a pure SPE, which is what that construction delivers. `k = 1` is the
grid `δ_N` itself; App. E ("its verification does not use the bid increment") and App. B ("From N
to m") give the finer grids and the dummy items. -/
theorem claim_B_6 (N : ℕ) (hN : 4 ≤ N) (d k : ℕ) (hk : 1 ≤ k) :
    ∃ b : Fin (nBid N) → Strategy (nBid N) (mOf N + d) (deltaOf N / k) 1,
      IsCompletion N d b ∧ IsPureSPE (prioBad N) (vBad N d) b := by sorry

end DraftPoA
