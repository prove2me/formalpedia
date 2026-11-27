-- Prove2me | Theorems.Thm_Erdos287_min_card_reciprocal_merge_obstruction
-- name    : Erdos287.min_card_reciprocal_merge_obstruction
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T23:42:42.477285+00:00
-- url     : https://prove2.me/theorems/c4f1d590-9a50-5649-9c04-3dbfd093c6fa
-- title:
--   An omitted reciprocal forces a blocking neighbor in a minimal gap-two set
-- statement:
--   Let a denominator set have reciprocal sum one, cover every adjacent pair in its interval, and have minimum cardinality among sets meeting those requirements and containing the left endpoint. If selected denominators $a,b$ with $b\ge a+2$ can be replaced exactly by an omitted $c$ in the interval, there is another omission next to $a$ or $b$.
-- source:
--   Erdős Problem 287. Exact reciprocal fusion in a cardinality-minimal denominator set.

import Mathlib

theorem Erdos287.min_card_reciprocal_merge_obstruction (D : Finset ℕ) (m M a b c : ℕ)
    (hm : m ∈ D) (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hmin : ∀ E : Finset ℕ, m ∈ E → E ⊆ Finset.Icc m M →
      (∀ x, m ≤ x → x + 1 ≤ M → x ∈ E ∨ x + 1 ∈ E) →
      (∑ n ∈ E, (1 : ℚ) / n = 1) → D.card ≤ E.card)
    (ha : a ∈ D) (hb : b ∈ D) (hma : m < a) (hab : a + 2 ≤ b)
    (hc : c ∈ Finset.Icc m M) (hcD : c ∉ D)
    (hmerge : (1 : ℚ) / a + 1 / b = 1 / c) :
    ∃ x ∈ Finset.Icc m M, x ∉ D ∧ x ≠ c ∧
      (x + 1 = a ∨ a + 1 = x ∨ x + 1 = b ∨ b + 1 = x) := by sorry
