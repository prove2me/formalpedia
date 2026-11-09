-- Prove2me | Theorems.Thm_EfronBroadcast_Main_bisect_complexity
-- name    : EfronBroadcast.Main.bisect_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:12.525019+00:00
-- url     : https://prove2.me/theorems/a035590d-8af8-4b60-bb09-1a010ac4c355
-- title:
--   Claim 19 — Bisect communication and rounds
-- statement:
--   A single constant $C>0$ works for every $n=2^k$, $t<n$, admissible SPLIT input, and $t$-bounded adaptive adversary. Let $H$ be the generated Bisect message history. Then
--
--   $$
--   \operatorname{rounds}(H)=2k,\qquad
--   \operatorname{bits}_q(H)\le C|P|k^2\quad(q\text{ correct}),\qquad
--   \operatorname{bits}_p(H)\le Ck^2\quad(p\in P\text{ correct}).
--   $$
--
--   The sender bound allows a corrupt receiver. The costs sum serialized messages actually sent in each role, including every destination copy, and the rounds count the recorded two-round layers. These are the resource clauses of Theorem 8.
--
--
--   Differences from the source:
--   - encoding: physical parties and value indices in [n], with n a power of two → n = 2^k, identities and value indices in Fin (2^k), bottom represented by Option.none; reason: zero-based relabeling preserves every instance, including n = 1
--   - encoding: Protocol 4 with synchronous delivery and arbitrary Byzantine behavior → the explicit Bisect local transitions generate a history for every corruption-time map and arbitrary history-dependent Byzantine strategy; reason: permanent corruption times include adaptive corruptions, and never-corrupted parties execute the printed local rules
--   - encoding: a sender set with a fixed order for ties and the integer input inequality |P| ≤ |W_p| − |A| → a duplicate-free sender list and the same inequality in integers; reason: the list records the source tie order and does not truncate subtraction
--   - reading: the pseudocode receives a count or child node without specifying a choice among multiple Byzantine packets → the first typed count or first valid child node in the incoming list is selected; reason: this completes malformed and multiple-message parsing; numerical count checks and child-only movement remain mandatory
--   - encoding: type-tagged node and count messages using O(k) bits each → explicit two-bit tags, self-delimiting binary integers and binary node strings, with costs equal to serialized lengths; reason: this fixes a wire convention within the source bounds; the same uniform constant covers all instances and executions
--   - encoding: O(k²) and O(|P|k²) communication → one positive natural constant C before all sizes, inputs, fault bounds and strategies, bounding actual sent bits by Ck² and C|P|k²; reason: the source estimates are uniform; k = 0 has no sends
--   - reading: separate receiver and sender communication bounds with no explicit overlap convention → node sends are charged to the receiver role and count sends to the sender role; reason: this follows the source proof message partition; if a physical identity runs both roles their physical cost is the sum
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 13, PDF p. 14, Claim 19; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Bisect
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Claim 19, p. 13 (PDF p. 14). Bounds use actual serialized sends. -/
theorem bisect_complexity :
    ∃ C : ℕ, 0 < C ∧ ∀ k t : ℕ, t < 2 ^ k → ∀ q : Party (2 ^ k),
      ∀ A : Finset (Fin (2 ^ k)), ∀ P : List (Party (2 ^ k)),
      ∀ W : Party (2 ^ k) → Finset (Fin (2 ^ k)), ∀ adv : BisectAdversary (2 ^ k),
      IsTBounded adv.corruptions t → SplitInput adv.corruptions A P W →
      let history := bisectHistory k q A P W adv k
      bisectRounds history = 2 * k ∧
      (IsCorrect adv.corruptions q → bisectReceiverBits history ≤ C * P.length * k ^ 2) ∧
      (∀ p ∈ P, IsCorrect adv.corruptions p → bisectSenderBits history p ≤ C * k ^ 2) := by sorry

end EfronBroadcast.Main
