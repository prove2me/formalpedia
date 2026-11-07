-- Prove2me | Theorems.Thm_FinsetParts_exists_parts_card_eq
-- name    : FinsetParts.exists_parts_card_eq
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T18:24:16.259047+00:00
-- url     : https://prove2.me/theorems/4fb162d9-536c-48de-9bf2-6d7ef08c4b2c
-- title:
--   Splitting a finite set into parts of prescribed sizes
-- statement:
--   Let $X$ be a finite set and let $b_1, \dots, b_n \in \mathbb{N}$ with $b_1 + \cdots + b_n = |X|$. Then there are subsets $Y_1, \dots, Y_n \subseteq X$ with $|Y_i| = b_i$ for all $i$ such that every element of $X$ lies in exactly one $Y_i$. That is, $X = Y_1 \sqcup \cdots \sqcup Y_n$.
-- source:
--   Standard combinatorics; used in J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, proof of Lemma 4.10, pp. 22–23 (partitions S = S_1 ∪ … ∪ S_n)

import Mathlib

namespace FinsetParts

/-- Splitting a finite set into parts of prescribed sizes: if `b₁ + ⋯ + bₙ = |X|`, then `X` is the disjoint union of subsets `Y₁, …, Yₙ` with `|Yᵢ| = bᵢ`. -/
theorem exists_parts_card_eq {α : Type*} [DecidableEq α] {n : ℕ} (X : Finset α)
    (b : Fin n → ℕ) (h : ∑ i, b i = X.card) :
    ∃ Y : Fin n → Finset α, (∀ i, Y i ⊆ X) ∧ (∀ i, (Y i).card = b i) ∧
      ∀ x ∈ X, ∃! i, x ∈ Y i := by sorry

end FinsetParts
