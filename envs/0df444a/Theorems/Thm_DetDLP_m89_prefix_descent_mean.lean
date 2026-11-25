-- Prove2me | Theorems.Thm_DetDLP_m89_prefix_descent_mean
-- name    : DetDLP.m89_prefix_descent_mean
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T16:52:50.909486+00:00
-- url     : https://prove2.me/theorems/ec5e27a1-3280-4fde-a6f0-37e7cc286dc5
-- title:
--   Conditional-mean invariant for deterministic prefix descent
-- statement:
--   Suppose each valid prefix splits into two children whose completion counts and total costs sum to those of the prefix. Empty prefixes have zero total cost. Starting from a nonempty prefix, repeatedly choosing a nonempty child of smaller mean reaches a valid nonempty leaf whose mean is no larger than the initial mean.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 Proof of Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_M89_SeedSelection
set_option autoImplicit false
open DetDLP.M89SeedSelection

theorem DetDLP.m89_prefix_descent_mean {α : Type*} (count : α → ℕ) (cost : α → ℝ) (children : α → Bool → α)
    (hz : ∀ a, count a = 0 → cost a = 0) (good : ℕ → α → Prop)
    (split : ∀ k a, good (k+1) a → count a = count (children a false) + count (children a true) ∧
      cost a = cost (children a false) + cost (children a true) ∧ ∀ b, good k (children a b))
    (k : ℕ) (a : α) (hg : good k a) (hne : 0 < count a) :
    let z := descend count cost children k a
    good 0 z ∧ 0 < count z ∧ cost z / count z ≤ cost a / count a := by sorry
