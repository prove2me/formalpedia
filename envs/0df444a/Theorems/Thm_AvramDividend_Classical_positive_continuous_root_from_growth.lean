-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_continuous_root_from_growth
-- name    : AvramDividend.Classical.positive_continuous_root_from_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:59:31.898515+00:00
-- url     : https://prove2.me/theorems/a7adc573-0be4-4fcb-82ad-6afd725f2bfd
-- title:
--   A continuous Laplace-type exponent crossing a positive level has a positive root
-- statement:
--   A continuous real Laplace-exponent-like function on [0,∞) beginning at zero and exceeding a positive killing rate q at some A>0 must attain q at a strictly positive φ≤A. This isolates the precise intermediate-value input for constructing the positive Esscher root Φ(q) after proving growth and continuity of the canonical Lévy–Khintchine exponent.
-- source:
--   Pinned Mathlib intermediate_value_Icc; essential continuity and large-parameter coercivity for the spectrally negative Lévy Laplace exponent.

import Mathlib
open Set

theorem AvramDividend.Classical.positive_continuous_root_from_growth
    (f : ℝ → ℝ) (q A : ℝ) (hq : 0 < q) (hA : 0 < A)
    (hcont : ContinuousOn f (Ici (0 : ℝ)))
    (h0 : f 0 = 0) (hgt : q < f A) :
    ∃ φ : ℝ, 0 < φ ∧ φ ≤ A ∧ f φ = q := by sorry
