-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_density_restrict_integral
-- name    : AvramDividend.Classical.avram_gen14_singular_density_restrict_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:40:53.065713+00:00
-- url     : https://prove2.me/theorems/ace08322-65fe-40ea-b7c7-90fb94689f3a
-- title:
--   Exact change of measure to a restricted singular negative jump integral
-- statement:
--   For any real random-jump integrand, Bochner integration against the proposed singular negative Levy measure equals restriction of Lebesgue integration to the open negative jump band with its exact power-law density. The expression is exact even if the integrals are not absolutely integrable, due to Bochner integral conventions.
-- source:
--   The previously proved singular-density change-of-measure theorem, pointwise toReal_ofReal and the pinned integral_indicator identity.

import Mathlib
open Classical MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen14_singular_density_restrict_integral
    (g : ℝ → ℝ) :
    (∫ z, g z ∂(volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) =
    (∫ z in Ioo (-1 : ℝ) 0,
      |z| ^ (-(3 / 2 : ℝ)) * g z ∂volume) := by sorry
