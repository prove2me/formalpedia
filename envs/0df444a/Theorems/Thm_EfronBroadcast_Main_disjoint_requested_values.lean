-- Prove2me | Theorems.Thm_EfronBroadcast_Main_disjoint_requested_values
-- name    : EfronBroadcast.Main.disjoint_requested_values
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:45.864361+00:00
-- url     : https://prove2.me/theorems/550b2ac7-6004-496f-b2a9-fe91e3846b44
-- title:
--   Claim 9 — disjoint requested values within each group
-- statement:
--   Let $n=2^k$ and $t<n$. Consider one invocation of Ladder with public graphs $G_c$ as in Lemma 2, receiver $q$, target $M\le n$, inputs $A,P$ and senders with inputs $W_p$, where every correct sender holds at least $M$ values and a correct receiver's $P$ is a set whose correct members are senders. Let the adversary be $t$-bounded, with ideal signatures. Suppose $q$ is correct and consider any attempt, with $A_{\mathrm{start}},d$ and the groups as at its start and $F,A_{\mathrm{end}}$ after it. For every member $p$ of a group with $p\notin F$,
--   $$
--   |L_p|=d,\qquad L_p\cap A_{\mathrm{start}}=\varnothing,\qquad L_p\subseteq A_{\mathrm{end}},
--   $$
--   and $L_p\cap L_{p'}=\varnothing$ for every other such member $p'$ of the same group. Disjointness is within a group only.
--
--   Differences from the source:
--   - encoding: n a power of two; parties and value indices in [n]; attempts and virtual indices from 1 → n = 2^k with Fin (2^k); zero-based rounds, attempts and virtual indices; ⊥ as Option.none; reason: relabelling preserves every instance
--   - encoding: adversary controlling corrupt parties in a synchronous network, signatures that cannot be forged, a binding vector commitment → all corruption-time maps and message tables of NetAdversary subject to Unforgeable, and the commitment represented by the committed list itself and charged the commitment length; reason: a deterministic protocol has one run per adversary, so this covers every adaptive strategy; correct parties use the list only through opening verification
--   - reading: the pseudocode receives a request with opening π, without stating the check or a choice among several messages → the first request from q for this attempt whose opening has position below m naming the sender is taken, and all requests heard feed the check of line 21; reason: §3.1 describes the membership proof as an opening of the sender position in the list of the claimed length
--   - reading: request messages ⟨request, s, j, ρ, |P|, d⟩_q without an instance → the signed request also contains an instance tag; reason: the broadcast protocol runs many invocations, and a signature from one must not count in another
--   - generalization: RET over V = [n], with senders holding K ≥ M values → any instance tag, including cert = some b in which data values carry signatures, and a separate size at least M per sender; reason: cert = none is the source case, and a common K is a special case of per-sender sizes
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 8, PDF p. 9, Claim 9; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Ladder
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Claim 9, p. 8 (PDF p. 9). `S₀`, `S₁` are the receiver's states at the start and the end of the
zero-based attempt `a`. -/
theorem disjoint_requested_values (k t : ℕ) (ht : t < 2 ^ k) (κ : ℕ) (I : LadderInstance (2 ^ k) k)
    (hG : ComparisonFamily κ k I.G) (adv : NetAdversary (2 ^ k) (LadderMsg (2 ^ k) k))
    (hadv : I.Admissible adv t) (hv : I.Valid adv.corruptions)
    (hq : IsCorrect adv.corruptions I.q) (a : ℕ) (ha : a < (k + 1) * attemptsPerScale k) :
    let S₀ := ladderRecvState I adv (a * attemptLength k)
    let S₁ := ladderRecvState I adv ((a + 1) * attemptLength k)
    ∀ g ∈ S₀.groups, ∀ p ∈ g, p ∉ S₁.F →
      (S₁.query p).card = S₀.d ∧ Disjoint (S₁.query p) S₀.A ∧ S₁.query p ⊆ S₁.A ∧
      ∀ p' ∈ g, p' ∉ S₁.F → p ≠ p' → Disjoint (S₁.query p) (S₁.query p') := by sorry

end EfronBroadcast.Main
