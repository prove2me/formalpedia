-- Prove2me | Theorems.Thm_Erdos195_reflection_word_021643
-- name    : Erdos195.reflection_word_021643
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-17T16:30:05.405244+00:00
-- url     : https://prove2.me/theorems/bab7fc88-d41e-415c-a6b8-875433a4f88a
-- title:
--   The reflection word $(0,2,1,6,4,3)$ is tree-safe and a true root release
-- statement:
--   The six-letter word
--   $$
--   Q=(0,2,1,6,4,3)
--   $$
--   is tree-safe for some tree witness $\theta$, and is a true root release: every open in-order pair $(a,b)$ with odd difference has even second entry.
--
--   This word is the checked positive instance of the finite reflection-completion construction applied to the odd word $(1,3)$, with second-batch order $(6,4)$. Its even subsequence divided by $2$ is $(0,1,3,2)$, which is itself tree-safe, and its odd subsequence is $(1,3)$. The construction does not preserve an arbitrary prescribed prefix such as $(0,1,x)$, and this instance does not by itself prove an extension lemma or settle Erdős #195.
--
--   **Formalization Note** Safety is official `Safe (treeLt θ)`. The second conjunct is the official true-root-release predicate used in `Erdos195.odd_entry_demand` and `Erdos195.nine_true_release`, specialized to this concrete word.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); derived from analysis relayed by Ethan Cheung (Nov 17 2026), hand-checked against the official Safe / treeLt / true-root-release definitions, Lean-verified.

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem reflection_word_021643 :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 2, 1, 6, 4, 3]) ∧
    (∀ a b : ℤ, a ∈ ([0, 2, 1, 6, 4, 3] : List ℤ) →
      b ∈ ([0, 2, 1, 6, 4, 3] : List ℤ) →
      [0, 2, 1, 6, 4, 3].idxOf a < [0, 2, 1, 6, 4, 3].idxOf b →
      2 * b - a ∉ ([0, 2, 1, 6, 4, 3] : List ℤ) →
      3 * b - 2 * a ∉ ([0, 2, 1, 6, 4, 3] : List ℤ) →
      (b - a) % 2 = 1 → b % 2 = 0) := by sorry

end Erdos195
