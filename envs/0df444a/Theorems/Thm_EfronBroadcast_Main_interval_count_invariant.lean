-- Prove2me | Theorems.Thm_EfronBroadcast_Main_interval_count_invariant
-- name    : EfronBroadcast.Main.interval_count_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:21.001002+00:00
-- url     : https://prove2.me/theorems/099fa4a9-dc59-4b54-b500-47543e6d5301
-- title:
--   Claim 16 — interval count invariant
-- statement:
--   Let $n=2^k$ and $t<n$. Run Bisect with receiver $q$, original inputs $A,P,(W_p)_{p\in P}$ satisfying the SPLIT input condition, and any adversary corrupting at most $t$ physical parties at arbitrary rounds. Suppose $q$ is correct. For every $1\le h\le k$, let $F,\sigma_x,w_x$ be the receiver state after round $2h$. Then every surviving sender $x\in P\setminus F$ satisfies
--
--   $$
--   w_x-|I_{\sigma_x}\cap A|\ \ge\
--   |\{y\in P\setminus F:\sigma_y=\sigma_x\}|.
--   $$
--
--   The subtraction is integer subtraction. This is an assertion about the state computed by the protocol, and is not imposed on reports or executions. It is the common invariant underlying the splitting conclusions.
--
--
--   Differences from the source:
--   - encoding: physical parties and value indices in [n], with n a power of two → n = 2^k, identities and value indices in Fin (2^k), bottom represented by Option.none; reason: zero-based relabeling preserves every instance, including n = 1
--   - encoding: Protocol 4 with synchronous delivery and arbitrary Byzantine behavior → the explicit Bisect local transitions generate a history for every corruption-time map and arbitrary history-dependent Byzantine strategy; reason: permanent corruption times include adaptive corruptions, and never-corrupted parties execute the printed local rules
--   - encoding: a sender set with a fixed order for ties and the integer input inequality |P| ≤ |W_p| − |A| → a duplicate-free sender list and the same inequality in integers; reason: the list records the source tie order and does not truncate subtraction
--   - reading: the pseudocode receives a count or child node without specifying a choice among multiple Byzantine packets → the first typed count or first valid child node in the incoming list is selected; reason: this completes malformed and multiple-message parsing; numerical count checks and child-only movement remain mandatory
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 11, PDF p. 12, Claim 16; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Bisect
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Claim 16, p. 11 (PDF p. 12), with integer subtraction. -/
theorem interval_count_invariant (k t : ℕ) (ht : t < 2 ^ k) (q : Party (2 ^ k))
    (A : Finset (Fin (2 ^ k))) (P : List (Party (2 ^ k)))
    (W : Party (2 ^ k) → Finset (Fin (2 ^ k))) (adv : BisectAdversary (2 ^ k))
    (ha : IsTBounded adv.corruptions t) (hi : SplitInput adv.corruptions A P W)
    (hq : IsCorrect adv.corruptions q) (h : ℕ) (hh₁ : 1 ≤ h) (hh₂ : h ≤ k) :
    let S := bisectState k q A P W adv h
    ∀ x ∈ P, x ∉ S.F →
      ((P.toFinset.filter (fun y => y ∉ S.F ∧ S.node y = S.node x)).card : ℤ) ≤
        (S.weight x : ℤ) - (((interval (S.node x)) ∩ A).card : ℤ) := by sorry

end EfronBroadcast.Main
