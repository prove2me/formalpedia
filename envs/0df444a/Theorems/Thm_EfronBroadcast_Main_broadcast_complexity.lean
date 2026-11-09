-- Prove2me | Theorems.Thm_EfronBroadcast_Main_broadcast_complexity
-- name    : EfronBroadcast.Main.broadcast_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:06.031118+00:00
-- url     : https://prove2.me/theorems/1f3d7c27-4280-4f7d-bfcb-f5c3bc9415b4
-- title:
--   Claim 7 — broadcast rounds and communication
-- statement:
--   For all constants $\kappa$ bounding the primitive sizes and $\kappa'$ bounding the graph degrees there is a constant $C$ such that, for $n=2^k$, $E\le t<n$, $\lambda>k$, public graphs as in Lemma 2, any leader, input and $t$-bounded adversary with ideal signatures running Protocol 1: the round count $1+3TE$ is at most $6t+1$, correct parties send nothing from then on, and the bits sent by correct parties are at most
--   $$
--   Cn^2k^4\lambda.
--   $$
--
--   Differences from the source:
--   - encoding: n a power of two, parties and signers in [n], bit 0 and 1 → n = 2^k, Fin (2^k), Bool with 0 = false; zero-based rounds, so that the source round after round 0 is round 1; reason: relabelling preserves every instance
--   - encoding: adversary controlling corrupt parties in a synchronous network, signatures that cannot be forged, a binding vector commitment → all corruption-time maps and message tables of NetAdversary subject to Unforgeable, and the commitment represented by the committed list itself and charged the commitment length; reason: a deterministic protocol has one run per adversary, so this covers every adaptive strategy; correct parties use the list only through opening verification
--   - reading: P_b is the set of direct accepters of the epoch; a non-leader accept message is valid only if the leader accept has been received → P_b keeps direct accepters only while the leader accept for b is held, since otherwise their messages are not valid; reason: this applies the validity convention of the Notation paragraph; correct accepters always carry the leader accept
--   - reading: signed Ladder messages inside Protocol 1 without an instance → requests are signed with their bit and epoch, and every Ladder message is wrapped with receiver, bit and epoch, charged O(k) bits; reason: parallel invocations must not be confused, and the wrapper stays within the source estimates
--   - encoding: O(n² log⁴(n) λ) with primitive sizes O(λ) and O(λ log L) → for all κ and κ′, one C before k, λ, the configuration, primitive sizes, input and adversary; reason: the source estimates are uniform
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 7, PDF p. 8, Claim 7; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Broadcast
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Claim 7, p. 7 (PDF p. 8), for `t ≥ E`. `κ` bounds the primitive sizes and `κ'` the graph degrees;
`C` is chosen before everything else. -/
theorem broadcast_complexity :
    ∀ κ κ' : ℕ, ∃ C : ℕ, 0 < C ∧ ∀ (k lam : ℕ) (cfg : BBConfig (2 ^ k) k), cfg.t < 2 ^ k →
      ladderE k ≤ cfg.t → k < lam → ComparisonFamily κ' k cfg.G →
      ∀ (Z : PrimitiveSizes), Z.Bounded κ lam → ∀ (input : Bool)
        (adv : NetAdversary (2 ^ k) (BBMsg (2 ^ k) k)), BBAdmissible cfg input adv →
      bbRounds k cfg.t ≤ 6 * cfg.t + 1 ∧
      (∀ p, IsCorrect adv.corruptions p → ∀ r, bbRounds k cfg.t ≤ r →
        sentAt (bbMachine cfg input) adv r p = []) ∧
      correctBits (bbMachine cfg input) adv (bbMsgBits Z) (bbRounds k cfg.t) ≤
        C * (2 ^ k) ^ 2 * k ^ 4 * lam := by sorry

end EfronBroadcast.Main
