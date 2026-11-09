-- Prove2me | Theorems.Thm_EfronBroadcast_Main_honest_leader_validity
-- name    : EfronBroadcast.Main.honest_leader_validity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:19.694501+00:00
-- url     : https://prove2.me/theorems/686360da-57cf-4d55-9f8d-4045ab55acb5
-- title:
--   Claim 5 — honest-leader validity
-- statement:
--   Let $n=2^k$, $E\le t<n$, with public graphs $G_c$ as in Lemma 2, any leader and input bit, and a $t$-bounded adversary with ideal signatures, running Protocol 1. If the leader is correct, then every correct party has the leader's input in $B$ after round 1 of step 1, and the other bit is never in the $B$ of any correct party.
--
--   Differences from the source:
--   - encoding: n a power of two, parties and signers in [n], bit 0 and 1 → n = 2^k, Fin (2^k), Bool with 0 = false; zero-based rounds, so that the source round after round 0 is round 1; reason: relabelling preserves every instance
--   - encoding: adversary controlling corrupt parties in a synchronous network, signatures that cannot be forged, a binding vector commitment → all corruption-time maps and message tables of NetAdversary subject to Unforgeable, and the commitment represented by the committed list itself and charged the commitment length; reason: a deterministic protocol has one run per adversary, so this covers every adaptive strategy; correct parties use the list only through opening verification
--   - reading: P_b is the set of direct accepters of the epoch; a non-leader accept message is valid only if the leader accept has been received → P_b keeps direct accepters only while the leader accept for b is held, since otherwise their messages are not valid; reason: this applies the validity convention of the Notation paragraph; correct accepters always carry the leader accept
--   - reading: signed Ladder messages inside Protocol 1 without an instance → requests are signed with their bit and epoch, and every Ladder message is wrapped with receiver, bit and epoch, charged O(k) bits; reason: parallel invocations must not be confused, and the wrapper stays within the source estimates
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 7, PDF p. 8, Claim 5; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Broadcast
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Claim 5, p. 7 (PDF p. 8). Round 1 of step 1 is round `1`, so its effect is in the state at the
start of round `2`. -/
theorem honest_leader_validity (k κ : ℕ) (cfg : BBConfig (2 ^ k) k) (ht : cfg.t < 2 ^ k) (hE : ladderE k ≤ cfg.t)
    (hG : ComparisonFamily κ k cfg.G) (input : Bool)
    (adv : NetAdversary (2 ^ k) (BBMsg (2 ^ k) k)) (hadv : BBAdmissible cfg input adv) (hℓ : IsCorrect adv.corruptions cfg.leader)
    (p : Party (2 ^ k)) (hp : IsCorrect adv.corruptions p) :
    input ∈ (bbState cfg input adv 2 p).B ∧
    ∀ r, (!input) ∉ (bbState cfg input adv r p).B := by sorry

end EfronBroadcast.Main
