-- Prove2me | Theorems.Thm_Complexity_contracting_recurrence_bounded
-- name    : Complexity.contracting_recurrence_bounded
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T08:48:43.836522+00:00
-- url     : https://prove2.me/theorems/97465eb9-f639-4225-83ed-182585c4547c
-- title:
--   Contracting recurrences at strictly smaller indices are uniformly bounded
-- statement:
--   Let f be any real-valued sequence on the natural numbers, let a and N be natural numbers, and let q and A be real constants with 0 ≤ q < 1. Suppose that for every n ≥ N with n ≥ a there is an index m with a ≤ m < n and
--
--   $$f(n)\le q f(m)+A.$$
--
--   Then there is a positive real constant C such that
--
--   $$f(n)\le C\qquad\text{for every }n\ge a.$$
--
--   This is the abstract strong-induction argument used at the end of Harvey–van der Hoeven's proof of Theorem 1.1, with their normalized running time as f. The statement allows the smaller index to depend on n and requires no monotonicity or nonnegativity of f. All finitely many indices below N are absorbed into C. It is a supporting generalization of that argument, rather than a separate numbered result in the paper.
-- source:
--   D. Harvey and J. van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193(2) (2021), 563-617, https://doi.org/10.4007/annals.2021.193.2.4; author preprint https://www.texmacs.org/joris/nlogn/nlogn.pdf, section 5.3, pp. 40-42.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

theorem Complexity.contracting_recurrence_bounded (f : ℕ → ℝ) (a N : ℕ) (q A : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hrec : ∀ n : ℕ, N ≤ n → a ≤ n →
      ∃ m : ℕ, a ≤ m ∧ m < n ∧ f n ≤ q * f m + A) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, a ≤ n → f n ≤ C := by sorry
