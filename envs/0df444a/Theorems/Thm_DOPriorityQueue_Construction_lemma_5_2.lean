-- Prove2me | Theorems.Thm_DOPriorityQueue_Construction_lemma_5_2
-- name    : DOPriorityQueue.Construction.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:18.852082+00:00
-- url     : https://prove2.me/theorems/5ed6b5a3-2516-4897-a092-a017e68c8d55
-- title:
--   Lemma 5.2 — A cutoff for exact prefetching
-- statement:
--   Let $V\ge1$ and let the live records have distinct encoded keys forming a finite set $L\subseteq[V]=\{1,\ldots,V\}$. Write $Q(x)=|\{k\in L: k\le x\}|$. Let $B,E\ge0$ be integers and suppose an estimate $\hat Q$ satisfies
--   $$\|\hat Q-Q\|_\infty=\max_{x\in[V]}|\hat Q(x)-Q(x)|\le 2E.$$
--   If $x\in[V]$ is the smallest integer satisfying $\hat Q(x)\ge B+2E$, then
--   $$B\le Q(x)\le B+4E+1.$$
--   If no such $x$ exists, the cutoff is $V$ and the total number of live records is less than $B+4E$.
--
--   In the construction, $B$ is the epoch length and $E=KZ+B$ the insertion-count error, and the first crossing found by the segment-tree search supplies a key prefix containing at least $B$ and at most $O(B)$ live records.
--
--   Differences from the source:
--   - generalization: the live keys of the core and the parameters B, E = KZ + B of Section 4.1 → any finite set of distinct keys in [V], any natural numbers B, E and any integer-valued estimate on [V]; reason: the core's live keys are distinct elements of [V] and its B, E are natural numbers, so the statement specializes to the source's
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), p. 21, Lemma 5.2

import Mathlib

set_option autoImplicit false

namespace DOPriorityQueue.Construction

/-- Guo--Hong--Li, STOC 2027 submission #538 (October 2026), p. 21, Lemma 5.2.
`live` is the set of distinct encoded keys of live records in `[V] = {1, …, V}`,
`Q x = #{k ∈ live | k ≤ x}`, and `Qhat` is within `2E` of `Q` on `[V]`.
If `x ∈ [V]` is the smallest with `Qhat x ≥ B + 2E`, then `B ≤ Q x ≤ B + 4E + 1`;
if there is no such `x`, the total number of live records is below `B + 4E`. -/
theorem lemma_5_2 (V B E : ℕ) (hV : 1 ≤ V) (live : Finset ℕ)
    (hlive : ∀ k ∈ live, 1 ≤ k ∧ k ≤ V) (Qhat : ℕ → ℤ)
    (hest : ∀ x, 1 ≤ x → x ≤ V →
      |Qhat x - ((live.filter (· ≤ x)).card : ℤ)| ≤ 2 * (E : ℤ)) :
    (∀ x, 1 ≤ x → x ≤ V → (B : ℤ) + 2 * E ≤ Qhat x →
      (∀ y, 1 ≤ y → y < x → Qhat y < (B : ℤ) + 2 * E) →
        B ≤ (live.filter (· ≤ x)).card ∧
          (live.filter (· ≤ x)).card ≤ B + 4 * E + 1) ∧
    ((∀ x, 1 ≤ x → x ≤ V → Qhat x < (B : ℤ) + 2 * E) →
      live.card < B + 4 * E) := by sorry

end DOPriorityQueue.Construction
