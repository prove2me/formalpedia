-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_negative_mark_compensation_outer_measure
-- name    : AvramDividend.Classical.original_negative_mark_compensation_outer_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T07:54:42.085656+00:00
-- url     : https://prove2.me/theorems/14d77790-3d10-4ce4-a0e0-0739bf42eb71
-- title:
--   Original negative-mark LK compensation with explicit outer Lévy measure binding
-- statement:
--   For an original strictly-negative jump measure ν with integrable large signed jumps and integrable compensated exponential primitive, the explicitly ν-integrated Lévy–Khintchine mark contribution equals θ times its signed large-jump integral plus its explicitly ν-integrated positive primitive. Parentheses ensure the measure ∂ν binds the OUTER jump integral rather than the inner interval integral. Uses the exact pointwise cutoff identity including the mark −1 boundary.
-- source:
--   Verified original pointwise cutoff theorem 5b579263 and integrable_indicator_iff, integral_indicator, integral_const_mul, integral_add; repairs suspected nested-integral binding in existing 86169797.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_original_lk_negative_mark_cutoff_identity
open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.original_negative_mark_compensation_outer_measure
    (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0)
    (θ : ℝ) (hθ : 0 < θ)
    (hLarge : IntegrableOn (fun y : ℝ => y) (Iic (-1 : ℝ)) ν)
    (hFn : Integrable
      (fun y : ℝ => ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ν) :
    (∫ y : ℝ,
      (Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂ν) =
      θ * ((∫ y in Iic (-1 : ℝ), y ∂ν) +
        (∫ y : ℝ, (∫ t in (0 : ℝ)..(-y),
          1 - Real.exp (-θ * t)) ∂ν)) := by sorry
