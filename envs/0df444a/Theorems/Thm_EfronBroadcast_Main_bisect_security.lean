-- Prove2me | Theorems.Thm_EfronBroadcast_Main_bisect_security
-- name    : EfronBroadcast.Main.bisect_security
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:26.385214+00:00
-- url     : https://prove2.me/theorems/26376f54-38c3-47f2-8b09-ae2fd5b1203b
-- title:
--   Theorem 8 — Bisect splitting security and resources
-- statement:
--   There is an absolute constant $C>0$ such that the following holds uniformly for $n=2^k$, $t<n$, every admissible SPLIT input and every adaptive adversary corrupting at most $t$ parties. The computed Bisect output satisfies both SPLIT properties: when the receiver $q$ is correct, all non-bottom outputs are distinct and outside $A$, and every correct sender $p$ has a non-bottom output in $W_p\setminus A$. Moreover,
--
--   $$
--   \operatorname{rounds}(H)=2k,\qquad
--   \operatorname{bits}_q(H)\le C|P|k^2\quad(q\text{ correct}),\qquad
--   \operatorname{bits}_p(H)\le Ck^2\quad(p\in P\text{ correct}).
--   $$
--
--   This combines the security and all resource conclusions of Theorem 8 for the physical-sender protocol. It does not assume any of them as fields of the algorithm or adversary.
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
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 8, PDF p. 9, Theorem 8; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Bisect
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Theorem 8, p. 8 (PDF p. 9), including both SPLIT properties and all resources. -/
theorem bisect_security :
    ∃ C : ℕ, 0 < C ∧ ∀ k t : ℕ, t < 2 ^ k → ∀ q : Party (2 ^ k),
      ∀ A : Finset (Fin (2 ^ k)), ∀ P : List (Party (2 ^ k)),
      ∀ W : Party (2 ^ k) → Finset (Fin (2 ^ k)), ∀ adv : BisectAdversary (2 ^ k),
      IsTBounded adv.corruptions t → SplitInput adv.corruptions A P W →
      let history := bisectHistory k q A P W adv k
      SplitOutput adv.corruptions q A P W (bisectOutput k q A P W adv) ∧
      bisectRounds history = 2 * k ∧
      (IsCorrect adv.corruptions q → bisectReceiverBits history ≤ C * P.length * k ^ 2) ∧
      (∀ p ∈ P, IsCorrect adv.corruptions p → bisectSenderBits history p ≤ C * k ^ 2) := by sorry

end EfronBroadcast.Main
