-- Prove2me | Theorems.Thm_EfronBroadcast_Main_sender_complexity
-- name    : EfronBroadcast.Main.sender_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:02.394725+00:00
-- url     : https://prove2.me/theorems/ee05dc03-c3f2-4426-9502-8028d6e6a95d
-- title:
--   Claim 15 — total correct-sender communication
-- statement:
--   For all constants $\kappa$ bounding the primitive sizes and $\kappa'$ bounding the graph degrees there is a constant $C$ such that, in every invocation as above with $k\ge1$ and for every $\lambda$, with no assumption on the receiver, the bits sent as senders by all correct parties together are at most
--   $$
--   C\,n\,k^4(\lambda+k).
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
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 11, PDF p. 12, Claim 15; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Ladder
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Claim 15, p. 11 (PDF p. 12), for any receiver: no hypothesis on `q` is made. `κ` bounds the
primitive sizes and `κ'` the graph degrees. `k ≥ 1` because the source's `k⁴` vanishes at `n = 1`. -/
theorem sender_complexity :
    ∀ κ κ' : ℕ, ∃ C : ℕ, 0 < C ∧ ∀ (k t lam : ℕ), 1 ≤ k → t < 2 ^ k → ∀ (Z : PrimitiveSizes),
      Z.Bounded κ lam → ∀ (I : LadderInstance (2 ^ k) k), ComparisonFamily κ' k I.G →
      ∀ adv : NetAdversary (2 ^ k) (LadderMsg (2 ^ k) k),
      I.Admissible adv t → I.Valid adv.corruptions →
      ladderSenderBits Z I adv ≤ C * 2 ^ k * k ^ 4 * (lam + k) := by sorry

end EfronBroadcast.Main
