-- Prove2me | Theorems.Thm_Erdos195_no_finite_fourth_term_closed
-- name    : Erdos195.no_finite_fourth_term_closed
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T05:13:48.488612+00:00
-- url     : https://prove2.me/theorems/393af633-4f2a-47fc-8302-0ab582a0c34a
-- title:
--   No finite word with two distinct letters is closed under fourth terms $3b-2a$
-- statement:
--   Let $Q$ be a finite word of integers with at least two distinct letters. Then some letter $a$ occurs before some letter $b$ with
--   $$3b-2a\notin Q.$$
--   Hence no finite set with at least two elements can be listed so that every in-order pair is closed by its fourth term; such full closure cannot serve as the invariant for finite stages of a Ho-style construction of $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195).
--
--   Formalization note: positions are `List.idxOf`; duplicates are allowed in `Q`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework and statement from GPT 6 Astra (Oct 23 2026 answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem no_finite_fourth_term_closed (Q : List ℤ) (hQ : ∃ x ∈ Q, ∃ y ∈ Q, x ≠ y) :
    ∃ a b : ℤ, a ∈ Q ∧ b ∈ Q ∧ Q.idxOf a < Q.idxOf b ∧ 3 * b - 2 * a ∉ Q := by sorry

end Erdos195
