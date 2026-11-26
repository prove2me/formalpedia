-- Prove2me | Theorems.Thm_BranchHeight1000_gram658_explicit_certificate_fields
-- name    : BranchHeight1000.gram658_explicit_certificate_fields
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-17T17:14:31.504472+00:00
-- url     : https://prove2.me/theorems/fb4b51a7-0807-4168-83f3-529814f5690c
-- title:
--   Explicit numerical certificate fields for Gram point 658
-- statement:
--   Let
--   \[S_M(w)=(w-\tfrac12)\log w-w+\tfrac12\log(2\pi)+\sum_{k=1}^{M}\frac{B_{2k}}{2k(2k-1)}w^{1-2k},\]
--   where \(B_j\) are the Bernoulli numbers and the complex logarithm is principal. Set
--   \[A(t)=\operatorname{Im}S_2(\tfrac14+\tfrac{it}{2})-\tfrac t2\log\pi,\qquad E(t)=\frac{60}{\pi^4}(\tfrac1{16}+\tfrac{t^2}{4})^{-2}.\]
--   For \(a=1012.85253\) and \(b=1012.85256\), the exact inequalities
--   \[658\pi-A(a)>E(a),\qquad A(b)-658\pi>E(b)\]
--   hold. The endpoints are nonnegative and both truncation orders equal the positive integer 2. These are the six numerical fields of the Gram-point certificate at index 658. This local certificate is one component of the height-1000 verification; it does not by itself certify all zeros in that range or imply the Riemann hypothesis.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033, Zeta/Certificate/GramPoint and Gram numerical data; Apache-2.0. Ordinary proof export and sharing by Desenvolvimento RH.

import Mathlib
open scoped BigOperators

theorem BranchHeight1000.gram658_explicit_certificate_fields :
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
  (0 ≤ (1012.85253 : ℝ)) ∧ (0 ≤ (1012.85256 : ℝ)) ∧
  (0 < (2 : ℕ)) ∧ (0 < (2 : ℕ)) ∧
  (658 * Real.pi - A 2 0 1012.85253 > E 2 0 1012.85253) ∧
  (A 2 0 1012.85256 - 658 * Real.pi > E 2 0 1012.85256) := by sorry
