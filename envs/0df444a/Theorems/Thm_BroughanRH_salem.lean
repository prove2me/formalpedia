-- Prove2me | Theorems.Thm_BroughanRH_salem
-- name    : BroughanRH.salem
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:25:36.250496+00:00
-- url     : https://prove2.me/theorems/400e1c06-6d9e-4934-baaf-4e6018ed645b
-- title:
--   Salem’s integral-equation uniqueness
-- statement:
--   Off the critical line, the only bounded measurable function annihilated by convolution with the logarithmic Salem kernel is zero almost everywhere. [Source](https://www.kevinbroughan.nz/ERH/ERHerrata.pdf).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 8.12 (corrected domain). https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem salem :
    ∀ σ : ℝ, 0 < σ → σ < 1 → σ ≠ 1/2 →
      let K (x : ℝ) := Real.exp (σ*x) / (Real.exp (Real.exp x) + 1)
      ∀ φ : ℝ → ℂ, Measurable φ → (∃ M : ℝ, ∀ x, ‖φ x‖ ≤ M) →
        (∀ x : ℝ, (∫ y : ℝ, (K (x-y) : ℂ) * φ y) = 0) →
        ∀ᵐ x : ℝ ∂MeasureTheory.volume, φ x = 0 := by sorry

end BroughanRH
