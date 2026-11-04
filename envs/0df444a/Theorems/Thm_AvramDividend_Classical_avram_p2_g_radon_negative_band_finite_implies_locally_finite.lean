-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_negative_band_finite_implies_locally_finite
-- name    : AvramDividend.Classical.avram_p2_g_radon_negative_band_finite_implies_locally_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:59:31.735425+00:00
-- url     : https://prove2.me/theorems/9cb44579-41a8-492b-9ed0-27b20dca9a1e
-- title:
--   Finite separated negative bands imply local finiteness of an intrinsic negative-mark mean measure
-- statement:
--   For any measure on the strictly negative real half-line, if every mark band below a fixed negative threshold has finite mass then the measure is locally finite. Every negative point has an open neighbourhood inside one of the finite separated bands. This is the Radon-regularity prerequisite for identifying the actual intrinsic Lévy mean-jump measure by compactly supported test functions; it does not assume any Lévy-rate or compensator identity.
-- source:
--   Mathlib.MeasureTheory.Measure.Typeclasses.Finite: IsLocallyFiniteMeasure.finiteAtNhds and Measure.FiniteAtFilter; applied to the actual original negative-mark mean measure after its independent separated-band finiteness proof.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p2_g_radon_negative_band_finite_implies_locally_finite
    (μ : Measure {x : ℝ // x < 0})
    (hBand : ∀ (ε : ℝ), 0 < ε →
      μ {x : {x : ℝ // x < 0} | (x : ℝ) ≤ -ε} < ⊤) :
    IsLocallyFiniteMeasure μ := by sorry
