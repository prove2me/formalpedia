-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_zero_cumulative_mass_implies_ae_support_gap
-- name    : AvramDividend.Classical.excursion_zero_cumulative_mass_implies_ae_support_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:17:09.266678+00:00
-- url     : https://prove2.me/theorems/2941aeed-3072-4e38-8dc5-9de7f16ec76c
-- title:
--   Zero cumulative measure below a height implies almost-sure support above it
-- statement:
--   If a Borel measure β gives no mass to the closed half-line (−∞,x], then β-almost every point y lies strictly above x. This is the exact measure-theoretic conversion required to apply the exponential Laplace upper bound from a putative gap in the killed ladder-potential cumulative measure.
-- source:
--   Pinned MeasureTheory.ae_iff and interval membership equivalences.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.excursion_zero_cumulative_mass_implies_ae_support_gap
    (β : Measure ℝ) (x : ℝ) (hzero : β (Iic x) = 0) :
    ∀ᵐ y : ℝ ∂β, x < y := by sorry
