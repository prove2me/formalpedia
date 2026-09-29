-- Prove2me | Theorems.Thm_Erdos1210_erdos_1210
-- name    : Erdos1210.erdos_1210
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:18:22.160505+00:00
-- url     : https://prove2.me/theorems/a47005a0-c658-491f-bb31-71e2d8de8a77
-- title:
--   Erdős Problem 1210: reciprocal gaps of a pairwise coprime set
-- statement:
--   **Erdős Problem 1210 (affirmative form).** Let $n\ge1$ and let $A\subseteq\{1,2,\dots,n-1\}$ be a set of integers that are pairwise coprime: $\gcd(a,b)=1$ for all distinct $a,b\in A$. Then
--   $$
--   \sum_{a\in A}\frac{1}{n-a}\;\le\;\sum_{p<n}\frac1p+O(1),
--   $$
--   where $p$ runs over primes and the implied constant is absolute (independent of $n$ and $A$).
--
--   Erdős asked whether this holds. By Mertens' theorem the right-hand side is $\log\log n+O(1)$; the question is whether a pairwise coprime set can push the left side above $\sum_{p<n}1/p$ by an unbounded amount.
--
--   **Formalization Note** The problem is stated as a yes/no question in the source; this item formalizes the affirmative answer. A negative answer is established by disproving this statement (proving its negation). Primes are `Nat.Prime`; the reciprocals are real numbers.
-- source:
--   Erdős Problem #1210, https://www.erdosproblems.com/1210 ; P. Erdős [Er77c] Problems and results on combinatorial number theory III, Number Theory Day (New York 1976), 1977, p.64 ; [Er80] A survey of problems in combinatorial number theory, Ann. Discrete Math. 1980, p.112. Lean encoding follows Formal Conjectures ErdosProblems/1210.lean, theorem erdos_1210 (affirmative direction of answer(sorry) ↔ ...).

import Mathlib
open Finset

namespace Erdos1210

theorem erdos_1210 :
    ∃ C : ℝ, ∀ n : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a < n) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b) →
      ∑ a ∈ A, (1 / ((n : ℝ) - a)) ≤
        (∑ p ∈ (range n).filter Nat.Prime, (1 / (p : ℝ))) + C := by sorry

end Erdos1210
