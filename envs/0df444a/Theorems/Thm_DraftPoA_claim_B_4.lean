-- Prove2me | Theorems.Thm_DraftPoA_claim_B_4
-- name    : DraftPoA.claim_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:12.241149+00:00
-- url     : https://prove2.me/theorems/1a29db72-5bdd-4cd9-ac52-3a18c82c57f6
-- title:
--   Claim B.4: with $F=\emptyset$ and $S=\emptyset$, taking $R'$ for free is optimal
-- statement:
--   Let $N\ge4$, $d\ge0$, $\delta'$ admissible and $b$ a completion. At every legal node $\nu$ at which an item remains, $F=\emptyset$ and $S=\emptyset$, taking $R'$ (with the remaining dummy items) for free is optimal: $A$ has no profitable one-shot deviation at $\nu$, and her continuation value under $b$ is $h|R'|$ on top of her utility at $\nu$.
--
--   Differences from the source:
--   - generalization: the instance with m(N) = N + r items and grid δ_N → every number d of dummy items and every grid δ′ ∈ {0} ∪ {δ_N/k : k ≥ 1}; reason: App. B (From N to m) and App. E (the verification does not use the bid increment) extend the check to these; d = 0, δ′ = δ_N is the source's case
--   - reading: at any node → at every legal node at which an item remains; reason: a one-shot deviation needs a round to be played
--   - reading: taking R′ for free is optimal → no profitable one-shot deviation of A, and continuation value h|R′|; reason: the claim is one of the one-shot checks of Claim B.6
--   - generalization: the claim → also A's continuation value h|R′|; reason: the profile's outcome at such nodes; used by Claim B.5
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), Claim B.4, p.22 (PDF 23)

import Mathlib
import Definitions.Def_DraftPoA_Auction
import Definitions.Def_DraftPoA_Equilibria
import Definitions.Def_DraftPoA_BadInstance

namespace DraftPoA

/-- Claim B.4 (A with F = ∅ and S = ∅), App. B, p.22 (PDF 23) (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

For `N ≥ 4`, any `d`, an admissible grid `δ′`, every completion `b` and every legal node `ν` at
which an item remains, `F = ∅` and `S = ∅`: taking `R′` (with the remaining dummy items) for free is
optimal, i.e. `A` has no profitable one-shot deviation at `ν`, and her continuation value under `b`
is `h|R′|` on top of her utility at `ν`. -/
theorem claim_B_4 (N : ℕ) (hN : 4 ≤ N) (d : ℕ) {δ' : ℝ} (hδ' : IsAdmissibleGrid N δ')
    (b : Fin (nBid N) → Strategy (nBid N) (mOf N + d) δ' 1) (hb : IsCompletion N d b)
    (ν : Node (nBid N) (mOf N + d)) (hν : IsNode δ' 1 ν) (hrem : (remaining ν).Nonempty)
    (hF : ¬ markerA ν) (hS : sinkLeft ν = ∅) :
    NoProfitableOneShot (prioBad N) (vBad N d) b (bidA N) ν ∧
    uFrom (prioBad N) (vBad N d) b ν (bidA N) =
      uAt (vBad N d (bidA N)) ν (bidA N) + hOf N * ((rentLeft ν).card : ℝ) := by sorry

end DraftPoA
