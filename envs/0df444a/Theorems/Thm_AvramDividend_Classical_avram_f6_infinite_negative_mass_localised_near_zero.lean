-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_infinite_negative_mass_localised_near_zero
-- name    : AvramDividend.Classical.avram_f6_infinite_negative_mass_localised_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:29:14.44363+00:00
-- url     : https://prove2.me/theorems/ef45ffc6-741c-4e37-9d13-5a2a5908fcf1
-- title:
--   Infinite negative Lévy intensity concentrates infinitely in every small near-zero interval
-- statement:
--   For a Borel measure on real jump sizes with infinite total negative mass and finite mass on the far negative tail at any δ>0, the remaining near-zero interval (-δ,0) has infinite mass. Applied to a spectrally negative Lévy driver, this identifies genuinely infinite negative small-jump activity, combining the Proved purejump UBV infinite intensity and Lévy truncation finiteness results.
-- source:
--   Generic measure partition; Proved 16a2d301 negative jump truncation finite and Proved b9b373fa purejump UBV infinite negative activity.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_infinite_negative_mass_localised_near_zero
    (ν : Measure ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hTotal : ν (Iio (0 : ℝ)) = ⊤)
    (hTail : ν (Iic (-δ)) < ⊤) :
    ν (Ioo (-δ) 0) = ⊤ := by sorry
