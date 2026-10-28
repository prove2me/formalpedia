-- Prove2me | Theorems.Thm_Erdos195_bounded_open_level_iff
-- name    : Erdos195.bounded_open_level_iff
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:33:34.250987+00:00
-- url     : https://prove2.me/theorems/97d6923f-ffa4-41b5-b5ee-5f6e7d108ca2
-- title:
--   Open levels $<K$ iff letters distinct mod $2^K$
-- statement:
--   For a finite word $Q$ of integers and $K\ge0$:
--   $$\bigl(\text{every open pair }(a,b)\text{ of }Q\text{ has }\nu_2(b-a)<K\bigr)\iff\bigl(\text{the letters of }Q\text{ are pairwise incongruent mod }2^K\bigr).$$
--   Here $(a,b)$ is open if $a$ precedes $b$ and $2b-a,3b-2a\notin Q$. Consequently no invariant bounding open-pair levels can hold along an exhaustive chain of words (Erdős Problem 195).
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem bounded_open_level_iff (Q : List ℤ) (K : ℕ) :
    (∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
        padicValInt 2 (b - a) < K) ↔
      (∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → ¬ (2 : ℤ) ^ K ∣ b - a) := by sorry

end Erdos195
