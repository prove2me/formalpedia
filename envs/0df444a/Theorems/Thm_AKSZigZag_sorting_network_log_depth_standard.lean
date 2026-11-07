-- Prove2me | Theorems.Thm_AKSZigZag_sorting_network_log_depth_standard
-- name    : AKSZigZag.sorting_network_log_depth_standard
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:19:38.408196+00:00
-- url     : https://prove2.me/theorems/fc878f0c-a5df-43b1-a737-fb0e537877c3
-- title:
--   Abstract and Introduction, p.1 — standard comparator networks of depth $O(\log n)$ and size $O(n\log n)$ sort every input
-- statement:
--   There is an absolute constant $c>0$ such that for every $n$ there is a comparator network on $n$ registers with the following properties:
--   1. every switch $(i,j)$ satisfies $i<j$ and puts the larger element into register $j$;
--   2. its depth (number of parallel steps) is at most $c\log_2 n$;
--   3. its size (number of switches) is at most $c\,n\log_2 n$;
--   4. it sorts every input: at the end the $i$-th smallest element is in the $i$-th register.
--
--   This is the Ajtai–Komlós–Szemerédi theorem in the model of the STOC paper. Depth $\log_2 n$ is a lower bound, and before this result the best known depth was Batcher's $O(\log^2 n)$.
--
--   This statement is strictly stronger than the open platform item `AKSSorting.Core.aks_sorting_network_log_depth`, which states the same bounds for networks whose switches may point either way. Forgetting condition 1 gives that item, so this goal is not a repost of it.
--
--   **Formalization Note** For $n\le1$ the bounds are $0$ and the empty network meets them.
--
--   Differences from the source:
--   - encoding: size O(n log n) and depth O(log n) → ∃ c > 0 before n with depth ≤ c·log₂ n and size ≤ c·n·log₂ n; reason: the definition of O(·) with one absolute constant; logarithms base 2 (§5)
--   - encoding: a deterministic sequence of switches, O(log n) delay (parallel) time → a list of parallel steps of disjoint switches (AKSSorting.Core.ComparatorNetwork); depth = number of steps, size = number of switches; reason: one parallel time unit is a set of disjoint switches; same networks
--   - reading: n and A powers of 2 (§5) → every n; reason: the abstract's O(·) ranges over all n; the power-of-2 assumption belongs to the construction of §5
--   - generalization: sorts permutations of 1,...,n ('We may assume the contents are also 1,...,n', p.3) → sorts every input from every linearly ordered type; reason: permutations of 1..n are such inputs
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, Abstract and Introduction, p.1

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork
import Definitions.Def_AKSZigZag_IsStandard

namespace AKSZigZag

open AKSSorting.Core

/-- **An O(n log n) sorting network** (Ajtai, Komlós, Szemerédi, *An O(n log n) Sorting
Network*, STOC 1983, doi:10.1145/800061.808726, Abstract and Introduction, p.1): "The purpose of
this paper is to describe a sorting network of size O(n log n) and depth O(log n)", where a
switch is a pair `(i, j)`, `i < j`, putting the larger content into register `j`.

There is an absolute constant `c > 0` such that for every `n` some comparator network on
`n` registers whose every comparator `(i, j)` has `i < j` has depth at most `c log₂ n`, has at
most `c n log₂ n` comparators, and sorts every input.

**Formalization Note.** `O(·)` is an explicit constant `c` chosen before `n`; `log₂` is
`Real.logb 2`. For `n ≤ 1` the bounds are `0` and the empty network meets them. Registers are `Fin n` (0-based). `Sorts` quantifies
over every linearly ordered type and every input. Dropping `IsStandard` gives the Open platform
item `AKSSorting.Core.aks_sorting_network_log_depth` (Combinatorica version, comparators in
either direction), which this statement therefore implies. -/
theorem sorting_network_log_depth_standard :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∃ N : ComparatorNetwork n,
      IsStandard N ∧
      (N.depth : ℝ) ≤ c * Real.logb 2 n ∧
      (N.size : ℝ) ≤ c * n * Real.logb 2 n ∧
      N.Sorts := by sorry

end AKSZigZag
