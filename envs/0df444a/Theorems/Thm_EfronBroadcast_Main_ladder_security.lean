-- Prove2me | Theorems.Thm_EfronBroadcast_Main_ladder_security
-- name    : EfronBroadcast.Main.ladder_security
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:11.737725+00:00
-- url     : https://prove2.me/theorems/63e1931f-d9d9-4e32-82b6-388eb1b65377
-- title:
--   Theorem 3 — Ladder security and all resource bounds
-- statement:
--   For all constants $\kappa$ bounding the primitive sizes and $\kappa'$ bounding the graph degrees there is a constant $C$ such that, for $n=2^k$, $t<n$, $\lambda>k$ and every invocation as above: the output satisfies the RET specification (Definition 2: $V\supseteq A$, $F\subseteq P$, delivery and resolution); $E=(k+1)(8k+8)(2k+3)$ is positive, depends on $k$ alone, and correct parties send nothing from round $E$ on; and for $k\ge1$,
--   $$
--   E\le Ck^3,\qquad \text{senders' bits}\le Cnk^4\lambda,\qquad \text{correct receiver's bits}\le C(|P|+|V\setminus A|)k^2\lambda.
--   $$
--
--   Differences from the source:
--   - encoding: n a power of two; parties and value indices in [n]; attempts and virtual indices from 1 → n = 2^k with Fin (2^k); zero-based rounds, attempts and virtual indices; ⊥ as Option.none; reason: relabelling preserves every instance
--   - encoding: adversary controlling corrupt parties in a synchronous network, signatures that cannot be forged, a binding vector commitment → all corruption-time maps and message tables of NetAdversary subject to Unforgeable, and the commitment represented by the committed list itself and charged the commitment length; reason: a deterministic protocol has one run per adversary, so this covers every adaptive strategy; correct parties use the list only through opening verification
--   - reading: the pseudocode receives a request with opening π, without stating the check or a choice among several messages → the first request from q for this attempt whose opening has position below m naming the sender is taken, and all requests heard feed the check of line 21; reason: §3.1 describes the membership proof as an opening of the sender position in the list of the claimed length
--   - reading: request messages ⟨request, s, j, ρ, |P|, d⟩_q without an instance → the signed request also contains an instance tag; reason: the broadcast protocol runs many invocations, and a signature from one must not count in another
--   - generalization: RET over V = [n], with senders holding K ≥ M values → any instance tag, including cert = some b in which data values carry signatures, and a separate size at least M per sender; reason: cert = none is the source case, and a common K is a special case of per-sender sizes
--   - encoding: O(·) in n and k, with primitive sizes O(λ) and O(λ log L) → for all κ bounding primitive sizes and all κ′ bounding graph degrees, one C before k, t, λ, inputs and adversary, and the bit bound at k ≥ 1; reason: the source estimates are uniform, and the source bound is 0 at k = 0 where the protocol can send messages, so it is meaningful from k = 1
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 6, PDF p. 7, Theorem 3; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Ladder
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Theorem 3, p. 6 (PDF p. 7). `ladderE k` is a function of `k` alone, so it is public and
independent of `M`. -/
theorem ladder_security :
    ∀ κ κ' : ℕ, ∃ C : ℕ, 0 < C ∧ ∀ (k t lam : ℕ), t < 2 ^ k → k < lam → ∀ (Z : PrimitiveSizes),
      Z.Bounded κ lam → ∀ (I : LadderInstance (2 ^ k) k), ComparisonFamily κ' k I.G →
      ∀ adv : NetAdversary (2 ^ k) (LadderMsg (2 ^ k) k),
      I.Admissible adv t → I.Valid adv.corruptions →
      let S := ladderRecvState I adv (ladderE k)
      RetOutput adv.corruptions I.q I.M I.A I.P S.A S.F ∧
      0 < ladderE k ∧
      (∀ p, IsCorrect adv.corruptions p → ∀ r, ladderE k ≤ r →
        sentAt (ladderMachine I) adv r p = []) ∧
      (1 ≤ k → ladderE k ≤ C * k ^ 3) ∧
      (1 ≤ k → ladderSenderBits Z I adv ≤ C * 2 ^ k * k ^ 4 * lam) ∧
      (1 ≤ k → IsCorrect adv.corruptions I.q →
        ladderReceiverBits Z I adv ≤ C * (I.P.length + (S.A \ I.A).card) * k ^ 2 * lam) := by sorry

end EfronBroadcast.Main
