-- Prove2me | Theorems.Thm_DraftPoA_claim_B_2
-- name    : DraftPoA.claim_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:11.716248+00:00
-- url     : https://prove2.me/theorems/e66b2b9a-b555-4b0a-a053-286352736f5d
-- title:
--   Claim B.2: no sink bidder has a profitable one-shot deviation
-- statement:
--   Let $N\ge4$, $d\ge0$, $\delta'$ admissible, $b$ a completion and $i$ a sink bidder ($C_j$ or $C'_j$). At every legal node $\nu$ at which an item remains:
--
--   1. under $b$, $i$'s continuation utility is $0$;
--   2. under every strategy of $i$, against the other bidders' strategies in $b$ (damaged subgames included), $i$'s continuation utility is at most $0$;
--   3. $i$ has no profitable one-shot deviation at $\nu$.
--
--   The twin's bid keeps sink item $j$ from selling below $\sigma_j$, so a sink bidder can never buy at a profit.
--
--   Differences from the source:
--   - generalization: the instance with m(N) = N + r items and grid δ_N → every number d of dummy items and every grid δ′ ∈ {0} ∪ {δ_N/k : k ≥ 1}; reason: App. B (From N to m) and App. E (the verification does not use the bid increment) extend the check to these; d = 0, δ′ = δ_N is the source's case
--   - reading: the profile, with A best-responding at damaged states with F = ∅ and S ≠ ∅ → every completion (A's action free there); reason: the claim's argument does not use A's action at those states (Claim B.6, first observation)
--   - reading: at any node → at every legal node at which an item remains; reason: a one-shot deviation needs a round to be played
--   - generalization: no profitable one-shot deviation → also the two facts of the proof: continuation utility 0 under b, at most 0 under every own strategy; reason: the proof states both; Claim B.6 and Remark B.7 (i) use them
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), Claim B.2, p.22 (PDF 23)

import Mathlib
import Definitions.Def_DraftPoA_Auction
import Definitions.Def_DraftPoA_Equilibria
import Definitions.Def_DraftPoA_BadInstance

namespace DraftPoA

/-- Claim B.2 (Sink bidders), App. B, p.22 (PDF 23), with the facts its proof establishes
(Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

For `N ≥ 4`, any `d`, an admissible grid `δ′`, every completion `b`, every sink bidder `i`
(`C_j` or `C′_j`, the bidders of index `≥ 2`) and every legal node `ν` at which an item remains:
under `b`, `i`'s continuation utility is `0`; under every strategy of `i` against the others'
strategies of `b` (including damaged subgames) it is at most `0`; hence `i` has no profitable
one-shot deviation at `ν`. -/
theorem claim_B_2 (N : ℕ) (hN : 4 ≤ N) (d : ℕ) {δ' : ℝ} (hδ' : IsAdmissibleGrid N δ')
    (b : Fin (nBid N) → Strategy (nBid N) (mOf N + d) δ' 1) (hb : IsCompletion N d b)
    (i : Fin (nBid N)) (hi : 2 ≤ i.val)
    (ν : Node (nBid N) (mOf N + d)) (hν : IsNode δ' 1 ν) (hrem : (remaining ν).Nonempty) :
    uFrom (prioBad N) (vBad N d) b ν i = uAt (vBad N d i) ν i ∧
    (∀ s : Strategy (nBid N) (mOf N + d) δ' 1,
      uFrom (prioBad N) (vBad N d) (Function.update b i s) ν i ≤ uAt (vBad N d i) ν i) ∧
    NoProfitableOneShot (prioBad N) (vBad N d) b i ν := by sorry

end DraftPoA
