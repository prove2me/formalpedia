-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_negative_mark_integral_compensation
-- name    : AvramDividend.Classical.original_negative_mark_integral_compensation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:33:49.326403+00:00
-- url     : https://prove2.me/theorems/86169797-1403-41a4-832c-a27292ff8d27
-- title:
--   Original Lévy-mark compensated integral as signed large marks plus finite jump primitive
-- statement:
--   For an arbitrary original Lévy jump measure supported on strictly negative marks, with finite large signed first moment and integrable nonnegative compensated jump primitive, integrate the exact LK truncation at y=-1. The integrated mark contribution is θ times the sum of the signed large-mark integral and the nonnegative primitive integral. The theorem uses the original mark measure and respects the boundary at -1, proving a substantive analytic step independent of the Lévy process's Gaussian and drift parameters.
-- source:
--   Exact original cutoff theorem 5b579263-d78e-4302-a64a-3621ecf687f3, Mathlib integrable_indicator_iff, integral_indicator, integral_add; leads to Open 7a6e6fc3-ceff-4a31-b81a-d1e2b60ae6aa.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_original_lk_negative_mark_cutoff_identity
open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.original_negative_mark_integral_compensation
    (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0)
    (θ : ℝ) (hθ : 0 < θ)
    (hLarge : IntegrableOn (fun y : ℝ => y) (Iic (-1 : ℝ)) ν)
    (hFn : Integrable
      (fun y : ℝ => ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ν) :
    (∫ y : ℝ,
      Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y ∂ν) =
      θ * ((∫ y in Iic (-1 : ℝ), y ∂ν) +
        (∫ y : ℝ, ∫ t in (0 : ℝ)..(-y),
          1 - Real.exp (-θ * t) ∂ν)) := by sorry
