-- Prove2me | Theorems.Thm_Erdos287_certified_omitted_prime_layer_mass
-- name    : Erdos287.certified_omitted_prime_layer_mass
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:13:20.8248+00:00
-- url     : https://prove2.me/theorems/ca6d3978-5eb8-5a34-9853-2b00241eff96
-- title:
--   Reciprocal mass of certified omitted prime layers above the square root
-- statement:
--   Let $m>1$ and $M$ be the least and greatest denominators in a strictly increasing unit-fraction representation of one. Let $P$ be a finite set of primes satisfying $p^2>M$ such that no selected denominator is a multiple of any $p\in P$. Then $1+\sum_{p\in P}p^{-1}\sum_{m\le ap\le M}a^{-1}\le\log(M/(m-1))$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.certified_omitted_prime_layer_mass (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ) (hfirst : 1 < f 0)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ f (k - 1) < p * p)
    (habsent : ∀ p ∈ P, ∀ i < k, ¬ p ∣ f i) :
    let m := f 0
    let M := f (k - 1)
    (1 : ℝ) + ∑ p ∈ P, (1 : ℝ) / p *
      ∑ a ∈ (Finset.Icc 1 (M / p)).filter (fun a => m ≤ a * p), (1 : ℝ) / a ≤
      Real.log ((M : ℝ) / ((m - 1 : ℕ) : ℝ)) := by sorry
