-- Prove2me | Theorems.Thm_AKSZigZag_section6_partitions
-- name    : AKSZigZag.section6_partitions
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:18:50.120871+00:00
-- url     : https://prove2.me/theorems/e55961ba-0a2a-4847-8056-fff0ca27061e
-- title:
--   §6, p.6 — $P_{t1}$, $P_{t2}$ are partitions into parts of at most three intervals
-- statement:
--   Let $A>10$ and $n$ be powers of $2$ and $0\le t\le\log_2 n$. Then:
--   1. the nonempty intervals of time $t$ are pairwise disjoint and cover all registers;
--   2. for $t\ge1$, each of $P_{t1}$ and $P_{t2}$ is a partition of the registers into pairwise disjoint parts (some possibly empty);
--   3. for $t\ge1$, every part of $P_{t1}$ and $P_{t2}$ is the union of at most three intervals of consecutive registers.
--
--   A node holds at most two intervals, so a cherry a priori has up to six. The claim is that they merge into at most three; this is what lets §7 describe the partitions without the tree.
--
--   Differences from the source:
--   - generalization: the parts consist of at most three intervals → adds the §8 claim that the intervals of time t partition the registers, and that P_t1, P_t2 are partitions; reason: both are stated by the paper (§6 'partition', §8 p.7) and implicit in the claim; the source's statement is clause 3
--   - encoding: partitions of (1,...,n) → lists of register sets, pairwise disjoint and covering Fin n, empty parts allowed; reason: empty cherries contribute nothing; same partitions
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §6, p.6 ("the above parts consist of at most six intervals, but they actually melt together to at most three"), §8, p.7 ("The intervals J form a partition of (1,...,n)")

import Mathlib
import Definitions.Def_AKSZigZag_RegisterAssignment

namespace AKSZigZag

/-- **The partitions** (AKS, STOC 1983, doi:10.1145/800061.808726, §6, p.6, and §8, p.7): "Since
the registers assigned to a particular node form at most two intervals, the above parts consist
of at most six intervals, but they actually melt together to at most three." and "The intervals
J form a partition of (1,...,n)".

Let `A > 10` and `n` be powers of 2 and `t ≤ log₂ n`. Then
1. the (nonempty) intervals of time `t` are pairwise disjoint and cover all registers;
2. for `t ≥ 1`, `P_t1` and `P_t2` are partitions of the registers (parts pairwise disjoint,
   covering everything; empty parts allowed), and every part is the union of at most three
   intervals `[a, b]` of registers.

**Formalization Note.** Partitions are lists of register sets; "pairwise disjoint" is
`List.Pairwise Disjoint`. -/
theorem section6_partitions (A n t : ℕ) (hA : 10 < A) (hApow : ∃ k, A = 2 ^ k)
    (hn : ∃ k, n = 2 ^ k) (ht : t ≤ Nat.log 2 n) :
    (((intervals A n t).map fun J => J.2.2).Pairwise Disjoint ∧
      ∀ r : Fin n, ∃ J ∈ intervals A n t, r ∈ J.2.2) ∧
    (1 ≤ t →
      (partition1 A n t).Pairwise Disjoint ∧ (∀ r : Fin n, ∃ P ∈ partition1 A n t, r ∈ P) ∧
      (partition2 A n t).Pairwise Disjoint ∧ (∀ r : Fin n, ∃ P ∈ partition2 A n t, r ∈ P) ∧
      ∀ P ∈ partition1 A n t ++ partition2 A n t, ∃ ivs : List (ℤ × ℤ), ivs.length ≤ 3 ∧
        P = (ivs.map fun ab => seg n ab.1 ab.2).foldr (· ∪ ·) ∅) := by sorry

end AKSZigZag
