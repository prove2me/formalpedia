-- Prove2me | Theorems.Thm_BranchHeight1000_gram655_left_stirling_margin
-- name    : BranchHeight1000.gram655_left_stirling_margin
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-17T14:48:02.46941+00:00
-- url     : https://prove2.me/theorems/56171b9f-ef46-4be9-9a35-8861345d7db3
-- title:
--   Gram point 655: left Stirling margin
-- statement:
--   Let
--   \[S_M(w)=(w-\tfrac12)\log w-w+\tfrac12\log(2\pi)+\sum_{k=1}^{M}\frac{B_{2k}}{2k(2k-1)}w^{1-2k},\]
--   where \(B_j\) are the Bernoulli numbers and the complex logarithm is principal. Set
--   \[A(t)=\operatorname{Im}S_2(\tfrac14+\tfrac{it}{2})-\tfrac t2\log\pi,\qquad E(t)=\frac{60}{\pi^4}(\tfrac1{16}+\tfrac{t^2}{4})^{-2}.\]
--   For \(a=1009.14258\), the exact left margin is
--   \[655\pi-A(a)>E(a).\]
--   This is the left endpoint condition for the Gram-point certificate at index 655. It is not a verification of all zeros up to height 1000.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033, Zeta/Certificate/GramPoint and Gram numerical data; Apache-2.0. Ordinary proof export and sharing by Desenvolvimento RH.

import Mathlib
open scoped BigOperators

theorem BranchHeight1000.gram655_left_stirling_margin :
  let S : ℕ → ℂ → ℂ := fun M w =>
    (w - 1 / 2) * Complex.log w - w + (1 / 2 : ℂ) * (Real.log (2 * Real.pi) : ℂ)
    + ∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ))
  let A : ℕ → ℕ → ℝ → ℝ := fun M N t =>
    (S M (1 / 4 + Complex.I * (t / 2) + N)
      - ∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * (t / 2) + j)).im
      - t / 2 * Real.log Real.pi
  let E : ℕ → ℕ → ℝ → ℝ := fun M N t =>
    (Nat.factorial (2 * M + 1) : ℝ) * 2 ^ (2 * M + 1) / (2 * M * (2 * Real.pi) ^ (2 * M))
    * ((1 / 4 + N) ^ 2 + (t / 2) ^ 2 : ℝ) ^ (-(M : ℤ))
  655 * Real.pi - A 2 0 1009.14258 > E 2 0 1009.14258 := by sorry
