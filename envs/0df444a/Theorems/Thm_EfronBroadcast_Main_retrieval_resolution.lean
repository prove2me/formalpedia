-- Prove2me | Theorems.Thm_EfronBroadcast_Main_retrieval_resolution
-- name    : EfronBroadcast.Main.retrieval_resolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:55.799205+00:00
-- url     : https://prove2.me/theorems/267ab882-eab7-41a4-9f04-ede7085d868f
-- title:
--   Claim 10 — retrieval resolution
-- statement:
--   Let $n=2^k$ and $t<n$. Consider one invocation of Ladder with public graphs $G_c$ as in Lemma 2, receiver $q$, target $M\le n$, inputs $A,P$ and senders with inputs $W_p$, where every correct sender holds at least $M$ values and a correct receiver's $P$ is a set whose correct members are senders. Let the adversary be $t$-bounded, with ideal signatures. If $q$ is correct and its final value set satisfies $|V|<M$, then every member of the original $P$ belongs to the final $F$.
--
--   Differences from the source:
--   - encoding: n a power of two; parties and value indices in [n]; attempts and virtual indices from 1 → n = 2^k with Fin (2^k); zero-based rounds, attempts and virtual indices; ⊥ as Option.none; reason: relabelling preserves every instance
--   - encoding: adversary controlling corrupt parties in a synchronous network, signatures that cannot be forged, a binding vector commitment → all corruption-time maps and message tables of NetAdversary subject to Unforgeable, and the commitment represented by the committed list itself and charged the commitment length; reason: a deterministic protocol has one run per adversary, so this covers every adaptive strategy; correct parties use the list only through opening verification
--   - reading: the pseudocode receives a request with opening π, without stating the check or a choice among several messages → the first request from q for this attempt whose opening has position below m naming the sender is taken, and all requests heard feed the check of line 21; reason: §3.1 describes the membership proof as an opening of the sender position in the list of the claimed length
--   - reading: request messages ⟨request, s, j, ρ, |P|, d⟩_q without an instance → the signed request also contains an instance tag; reason: the broadcast protocol runs many invocations, and a signature from one must not count in another
--   - generalization: RET over V = [n], with senders holding K ≥ M values → any instance tag, including cert = some b in which data values carry signatures, and a separate size at least M per sender; reason: cert = none is the source case, and a common K is a special case of per-sender sizes
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 9, PDF p. 10, Claim 10; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Ladder
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Claim 10, p. 9 (PDF p. 10). -/
theorem retrieval_resolution (k t : ℕ) (ht : t < 2 ^ k) (κ : ℕ) (I : LadderInstance (2 ^ k) k)
    (hG : ComparisonFamily κ k I.G) (adv : NetAdversary (2 ^ k) (LadderMsg (2 ^ k) k))
    (hadv : I.Admissible adv t) (hv : I.Valid adv.corruptions)
    (hq : IsCorrect adv.corruptions I.q) :
    let S := ladderRecvState I adv (ladderE k)
    S.A.card < I.M → ∀ p ∈ I.P, p ∈ S.F := by sorry

end EfronBroadcast.Main
