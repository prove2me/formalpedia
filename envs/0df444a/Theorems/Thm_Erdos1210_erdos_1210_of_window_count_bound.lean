-- Prove2me | Theorems.Thm_Erdos1210_erdos_1210_of_window_count_bound
-- name    : Erdos1210.erdos_1210_of_window_count_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:10:30.897926+00:00
-- url     : https://prove2.me/theorems/49540549-c8ad-4ffe-922e-fb375f839733
-- title:
--   Window counting bound implies Erdős 1210 (partial summation)
-- statement:
--   Suppose there is a constant $K$ such that for all $n$, all pairwise coprime $A\subseteq[1,n)$ and all $x\ge2$,
--   $$
--   |A\cap[n-x,n)|\le\pi(x)+\frac{Kx}{(\log x)^2}.
--   $$
--   Then the affirmative answer to Erdős Problem 1210 holds: there is $C$ with $\sum_{a\in A}\frac1{n-a}\le\sum_{p<n}\frac1p+C$ for all $n$ and all pairwise coprime $A\subseteq[1,n)$.
--
--   This is the partial-summation step of the reduction discussed on the erdosproblems.com forum. The hypothesis itself is not known: as noted in that discussion, it would imply an inequality of the form $\pi(x+y)\le\pi(x)+\pi(y)+O(y/(\log y)^2)$ (compare Problem 855). The milestone isolates the implication, which is unconditional.
--
--   **Formalization Note** The window $[n-x,n)$ is encoded as $a\ge n-x$ with truncated subtraction, together with the standing hypothesis $a<n$.
-- source:
--   erdosproblems.com forum thread for Problem 1210, https://www.erdosproblems.com/forum/thread/1210 , comment by T. Bloom (8 Apr 2026, relaying a suggested argument): the bound |A ∩ [n−x,n)| ≤ π(x) + O(x/(log x)^2) for all x implies the problem 'by partial summation'; follow-up by N. Sothanaphan (8 Apr 2026) on why the bound itself is not known.

import Mathlib
open Finset

namespace Erdos1210

theorem erdos_1210_of_window_count_bound
    (h : ∃ K : ℝ, ∀ n : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a < n) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b) →
      ∀ x : ℕ, 2 ≤ x →
        ((A.filter (fun a => n - x ≤ a)).card : ℝ) ≤
          (Nat.primeCounting x : ℝ) + K * x / (Real.log x) ^ 2) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a < n) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b) →
      ∑ a ∈ A, (1 / ((n : ℝ) - a)) ≤
        (∑ p ∈ (range n).filter Nat.Prime, (1 / (p : ℝ))) + C := by sorry

end Erdos1210
