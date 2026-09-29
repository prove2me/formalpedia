-- Prove2me | Theorems.Thm_Erdos142_apFree_iff
-- name    : Erdos142.apFree_iff
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:31:30.26372+00:00
-- url     : https://prove2.me/theorems/07a0df8a-5a69-438b-aeb1-84d74e4195a4
-- title:
--   Elementary characterisation of progression-freeness
-- statement:
--   For every $k \ge 2$ and every finite set $A$ of natural numbers, the two formulations of progression-freeness agree:
--
--   $$A \text{ contains no } (a, d) \text{ with } d > 0 \text{ and } a + id \in A \text{ for all } i < k \iff A \text{ is free of arithmetic progressions of length } k .$$
--
--   The right-hand side is the source definition: every subset of $A$ that is an arithmetic progression of length $k$ forces $k \le 1$. The left-hand side is the elementary one: there is no first term $a$ and common difference $d > 0$ with all of $a, a+d, \dots, a+(k-1)d$ in $A$.
--
--   The two differ in how they express non-triviality. The source definition demands that the progression, as a *set*, have exactly $k$ elements, which for $k \ge 2$ forces the common difference to be non-zero; the elementary definition imposes $d > 0$ directly. The hypothesis $k \ge 2$ cannot be dropped: at $k \le 1$ the source convention makes every set free of length-$k$ progressions, while the elementary predicate does not.
--
--   This is the mission's working lemma. Every later milestone is stated in terms of $r_k$, which is defined through the source predicate, but is proved by manipulating explicit progressions; this equivalence is what licenses that move, and it removes the cardinality side condition in $\mathbb{N} \cup \{\infty\}$ from all downstream reasoning.
-- source:
--   Google DeepMind, formal-conjectures, FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean, definition Set.IsAPOfLengthFree, https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/142.lean ; Erdős Problem #142, https://www.erdosproblems.com/142 (cited there as [Er80, p.92], [Er81, p.4], [Er97c], [Va99, 1.27])

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos142

theorem apFree_iff (k : ℕ) (hk : 2 ≤ k) (A : Finset ℕ) :
    APFree k A ↔ IsAPOfLengthFree (A : Set ℕ) k := by sorry

end Erdos142
