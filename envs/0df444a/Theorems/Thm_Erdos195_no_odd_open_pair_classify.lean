-- Prove2me | Theorems.Thm_Erdos195_no_odd_open_pair_classify
-- name    : Erdos195.no_odd_open_pair_classify
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T03:10:00.827594+00:00
-- url     : https://prove2.me/theorems/f31e8b46-f2d3-48ff-9eba-b22e29dcf213
-- title:
--   Words without opposite-parity open pairs are almost single-parity
-- statement:
--   Let $Q$ be a finite word of integers. An in-order pair of $Q$ is a pair $(a,b)$ of letters with $a$ occurring before $b$; it is open if neither continuation $2b-a$ nor $3b-2a$ is a letter of $Q$. Suppose every in-order pair $(a,b)$ of $Q$ with $b-a$ odd is closed, i.e. $2b-a\in Q$ or $3b-2a\in Q$. Then either all letters of $Q$ have the same parity, or, writing $A=\min Q$ and $B=\max Q$,
--   $$A\equiv B \pmod 2\quad\text{and every letter } x \text{ with } x\not\equiv A \pmod 2 \text{ satisfies } x=\tfrac{A+B}{2} \text{ and occurs after both } A \text{ and } B.$$
--   So a word without opposite-parity open pairs contains at most one letter of the minority parity (example: $(0,2,1)$). No safety assumption is needed. In the study of $\varepsilon$-safe words (Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$, Erdős Problem 195), open pairs force digits of $\varepsilon$, and this shows that the lowest digit $\varepsilon_0$ is forced in essentially every mixed-parity word.
--
--   Formalization note: "before" is comparison of `List.idxOf`; the conclusion is stated as a disjunction with explicit $A,B\in Q$ bounding all letters and `2 * x = A + B`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem no_odd_open_pair_classify (Q : List ℤ)
    (hno : ∀ a ∈ Q, ∀ b ∈ Q, Q.idxOf a < Q.idxOf b → (b - a) % 2 = 1 →
      2 * b - a ∈ Q ∨ 3 * b - 2 * a ∈ Q) :
    (∀ x ∈ Q, ∀ y ∈ Q, x % 2 = y % 2) ∨
    ∃ A B : ℤ, A ∈ Q ∧ B ∈ Q ∧ (∀ z ∈ Q, A ≤ z ∧ z ≤ B) ∧ A % 2 = B % 2 ∧
      ∀ x ∈ Q, x % 2 ≠ A % 2 → 2 * x = A + B ∧ Q.idxOf A < Q.idxOf x ∧ Q.idxOf B < Q.idxOf x := by sorry

end Erdos195
