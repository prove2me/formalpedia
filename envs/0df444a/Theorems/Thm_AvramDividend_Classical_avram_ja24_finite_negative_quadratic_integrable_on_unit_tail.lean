-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja24_finite_negative_quadratic_integrable_on_unit_tail
-- name    : AvramDividend.Classical.avram_ja24_finite_negative_quadratic_integrable_on_unit_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:11:56.25642+00:00
-- url     : https://prove2.me/theorems/ce7aa226-3728-4e4e-a747-f5a0836dcb30
-- title:
--   Finite negative activity makes quadratic mark integrable on unit tail
-- statement:
--   Any measure with finite negative half-line mass integrates the bounded square z squared on the open interval from a to zero whenever a is at least negative one.
-- source:
--   Original Gaussian strip variance deterministic integrability for e5df71c0 and 6aac909c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ja24_finite_negative_quadratic_integrable_on_unit_tail
    (μ : Measure ℝ) (a : ℝ)
    (ha : (-1 : ℝ) ≤ a)
    (hFinite : μ (Iio (0 : ℝ)) ≠ ⊤) :
    IntegrableOn (fun z : ℝ => z ^ 2) (Ioo a 0) μ := by sorry
