-- Prove2me | Theorems.Thm_DraftPoA_claim_B_1
-- name    : DraftPoA.claim_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:15.614782+00:00
-- url     : https://prove2.me/theorems/f9b5bcf6-4fa3-4bdc-a4a1-fada4977f535
-- title:
--   Claim B.1: $Q$ has no profitable one-shot deviation
-- statement:
--   Let $N\ge4$, $d\ge0$, $\delta'$ admissible and $b$ a completion. At every legal node $\nu$ at which an item remains:
--
--   1. under $b$, $Q$'s continuation utility is $0$ (her utility at the end of the play equals her utility at $\nu$);
--   2. under every profile whatsoever, $Q$'s continuation utility is at most $0$;
--   3. $Q$ has no profitable one-shot deviation at $\nu$.
--
--   $Q$ values nothing, so the threat costs it nothing: under the profile it never wins.
--
--   Differences from the source:
--   - generalization: the instance with m(N) = N + r items and grid δ_N → every number d of dummy items and every grid δ′ ∈ {0} ∪ {δ_N/k : k ≥ 1}; reason: App. B (From N to m) and App. E (the verification does not use the bid increment) extend the check to these; d = 0, δ′ = δ_N is the source's case
--   - reading: the profile, with A best-responding at damaged states with F = ∅ and S ≠ ∅ → every completion (A's action free there); reason: the claim's argument does not use A's action at those states (Claim B.6, first observation)
--   - reading: at any node → at every legal node at which an item remains; reason: a one-shot deviation needs a round to be played
--   - generalization: no profitable one-shot deviation → also the two facts of the proof: continuation utility 0 under b, at most 0 under every profile; reason: the proof states both; Claim B.6 and Remark B.7 (i) use them
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), Claim B.1, p.22 (PDF 23)

import Mathlib
import Definitions.Def_DraftPoA_Auction
import Definitions.Def_DraftPoA_Equilibria
import Definitions.Def_DraftPoA_BadInstance

namespace DraftPoA

/-- Claim B.1 (Q), App. B, p.22 (PDF 23), with the facts its proof establishes
(Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

For `N ≥ 4`, any number `d` of dummy items, an admissible grid `δ′`, every completion `b` and every
legal node `ν` at which an item remains: under `b`, `Q`'s continuation utility is `0` (her utility at
the end equals her utility at `ν`); under every profile whatsoever `Q`'s continuation utility is at
most `0`; hence `Q` has no profitable one-shot deviation at `ν`. -/
theorem claim_B_1 (N : ℕ) (hN : 4 ≤ N) (d : ℕ) {δ' : ℝ} (hδ' : IsAdmissibleGrid N δ')
    (b : Fin (nBid N) → Strategy (nBid N) (mOf N + d) δ' 1) (hb : IsCompletion N d b)
    (ν : Node (nBid N) (mOf N + d)) (hν : IsNode δ' 1 ν) (hrem : (remaining ν).Nonempty) :
    uFrom (prioBad N) (vBad N d) b ν (bidQ N) = uAt (vBad N d (bidQ N)) ν (bidQ N) ∧
    (∀ b' : Fin (nBid N) → Strategy (nBid N) (mOf N + d) δ' 1,
      uFrom (prioBad N) (vBad N d) b' ν (bidQ N) ≤ uAt (vBad N d (bidQ N)) ν (bidQ N)) ∧
    NoProfitableOneShot (prioBad N) (vBad N d) b (bidQ N) ν := by sorry

end DraftPoA
