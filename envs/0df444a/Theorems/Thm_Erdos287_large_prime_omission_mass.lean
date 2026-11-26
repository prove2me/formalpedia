-- Prove2me | Theorems.Thm_Erdos287_large_prime_omission_mass
-- name    : Erdos287.large_prime_omission_mass
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:00:45.752709+00:00
-- url     : https://prove2.me/theorems/4be7baf7-bcb1-5351-87ff-e42120ff4ed8
-- title:
--   Reciprocal mass of disjoint omitted large-prime layers
-- statement:
--   Let $m,M$ be the smallest and largest denominators in a strictly increasing representation of one by positive unit fractions with $m>1$. Let $\mathcal A$ be a finite prime set satisfying $\lfloor M/p\rfloor\operatorname{lcm}(1,\ldots,\lfloor M/p\rfloor)<p$ for every $p\in\mathcal A$. Then $1+\sum_{p\in\mathcal A}p^{-1}\sum_{m\le ap\le M}a^{-1}\le\log(M/(m-1))$.
-- source:
--   E. S. Croot III, On unit fractions with denominators in short intervals, Acta Arithmetica 99 (2001), Section III, https://ecroot.math.gatech.edu/fractions_intervals.pdf.

import Mathlib

theorem Erdos287.large_prime_omission_mass (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ) (hfirst : 1 < f 0)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hsmall : ∀ p ∈ P, (f (k - 1) / p) * Nat.lcmUpto (f (k - 1) / p) < p) :
    let m := f 0
    let M := f (k - 1)
    (1 : ℝ) + ∑ p ∈ P, (1 : ℝ) / p *
      ∑ a ∈ (Finset.Icc 1 (M / p)).filter (fun a => m ≤ a * p), (1 : ℝ) / a ≤
      Real.log ((M : ℝ) / ((m - 1 : ℕ) : ℝ)) := by sorry
