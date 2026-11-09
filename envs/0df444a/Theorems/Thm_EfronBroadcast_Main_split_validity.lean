-- Prove2me | Theorems.Thm_EfronBroadcast_Main_split_validity
-- name    : EfronBroadcast.Main.split_validity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:12.780288+00:00
-- url     : https://prove2.me/theorems/fcb519cd-da7e-446f-b0a8-a028be621654
-- title:
--   Claim 18 — correct-sender output validity
-- statement:
--   Let $n=2^k$ and $t<n$. Run Bisect with receiver $q$, original inputs $A,P,(W_p)_{p\in P}$ satisfying the SPLIT input condition, and any adversary corrupting at most $t$ physical parties at arbitrary rounds. If $q$ is correct, every correct sender $p\in P$ has
--
--   $$
--   j_p\ne\bot,\qquad j_p\in W_p\setminus A.
--   $$
--
--   The output is computed from the final surviving leaf, rather than chosen using this property. This is the validity property required by SPLIT.
--
--
--   Differences from the source:
--   - encoding: physical parties and value indices in [n], with n a power of two → n = 2^k, identities and value indices in Fin (2^k), bottom represented by Option.none; reason: zero-based relabeling preserves every instance, including n = 1
--   - encoding: Protocol 4 with synchronous delivery and arbitrary Byzantine behavior → the explicit Bisect local transitions generate a history for every corruption-time map and arbitrary history-dependent Byzantine strategy; reason: permanent corruption times include adaptive corruptions, and never-corrupted parties execute the printed local rules
--   - encoding: a sender set with a fixed order for ties and the integer input inequality |P| ≤ |W_p| − |A| → a duplicate-free sender list and the same inequality in integers; reason: the list records the source tie order and does not truncate subtraction
--   - reading: the pseudocode receives a count or child node without specifying a choice among multiple Byzantine packets → the first typed count or first valid child node in the incoming list is selected; reason: this completes malformed and multiple-message parsing; numerical count checks and child-only movement remain mandatory
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 12, PDF p. 13, Claim 18; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Bisect
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Claim 18, p. 12 (PDF p. 13). -/
theorem split_validity (k t : ℕ) (ht : t < 2 ^ k) (q : Party (2 ^ k))
    (A : Finset (Fin (2 ^ k))) (P : List (Party (2 ^ k)))
    (W : Party (2 ^ k) → Finset (Fin (2 ^ k))) (adv : BisectAdversary (2 ^ k))
    (ha : IsTBounded adv.corruptions t) (hi : SplitInput adv.corruptions A P W)
    (hq : IsCorrect adv.corruptions q) :
    ∀ p ∈ P, IsCorrect adv.corruptions p →
      ∃ v, bisectOutput k q A P W adv p = some v ∧ v ∈ W p ∧ v ∉ A := by sorry

end EfronBroadcast.Main
