-- Prove2me | Theorems.Thm_EfronBroadcast_Main_split_distinctness
-- name    : EfronBroadcast.Main.split_distinctness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:24.265935+00:00
-- url     : https://prove2.me/theorems/97161728-56ac-4a8a-b200-5b02b6c9d6ea
-- title:
--   Claim 17 — split output distinctness
-- statement:
--   Let $n=2^k$ and $t<n$. Run Bisect with receiver $q$, original inputs $A,P,(W_p)_{p\in P}$ satisfying the SPLIT input condition, and any adversary corrupting at most $t$ physical parties at arbitrary rounds. If $q$ is correct, write $j_p\in[n]\cup\{\bot\}$ for the computed final outputs. Then
--
--   $$
--   j_p\ne\bot\ \Longrightarrow\ j_p\notin A,\qquad
--   j_p=j_{p'}\ne\bot\ \Longrightarrow\ p=p'.
--   $$
--
--   This covers Byzantine as well as correct senders. It asserts the split property of Definition 3 for Bisect's actual output.
--
--
--   Differences from the source:
--   - encoding: physical parties and value indices in [n], with n a power of two → n = 2^k, identities and value indices in Fin (2^k), bottom represented by Option.none; reason: zero-based relabeling preserves every instance, including n = 1
--   - encoding: Protocol 4 with synchronous delivery and arbitrary Byzantine behavior → the explicit Bisect local transitions generate a history for every corruption-time map and arbitrary history-dependent Byzantine strategy; reason: permanent corruption times include adaptive corruptions, and never-corrupted parties execute the printed local rules
--   - encoding: a sender set with a fixed order for ties and the integer input inequality |P| ≤ |W_p| − |A| → a duplicate-free sender list and the same inequality in integers; reason: the list records the source tie order and does not truncate subtraction
--   - reading: the pseudocode receives a count or child node without specifying a choice among multiple Byzantine packets → the first typed count or first valid child node in the incoming list is selected; reason: this completes malformed and multiple-message parsing; numerical count checks and child-only movement remain mandatory
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 12, PDF p. 13, Claim 17; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Bisect
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Claim 17, p. 12 (PDF p. 13). -/
theorem split_distinctness (k t : ℕ) (ht : t < 2 ^ k) (q : Party (2 ^ k))
    (A : Finset (Fin (2 ^ k))) (P : List (Party (2 ^ k)))
    (W : Party (2 ^ k) → Finset (Fin (2 ^ k))) (adv : BisectAdversary (2 ^ k))
    (ha : IsTBounded adv.corruptions t) (hi : SplitInput adv.corruptions A P W)
    (hq : IsCorrect adv.corruptions q) :
    let j := bisectOutput k q A P W adv
    (∀ p ∈ P, ∀ v, j p = some v → v ∉ A) ∧
    (∀ p ∈ P, ∀ p' ∈ P, ∀ v, j p = some v → j p' = some v → p = p') := by sorry

end EfronBroadcast.Main
