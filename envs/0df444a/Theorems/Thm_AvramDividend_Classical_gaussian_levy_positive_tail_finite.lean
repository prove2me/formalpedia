-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_levy_positive_tail_finite
-- name    : AvramDividend.Classical.gaussian_levy_positive_tail_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:02:40.765692+00:00
-- url     : https://prove2.me/theorems/01ae7811-cdc5-4836-80f8-561620f94671
-- title:
--   Finite Lévy jump intensity above any positive threshold
-- statement:
--   For a Lévy measure on positive jump magnitudes whose integral of min(1,z²) is finite, every positive tail [ε,∞), ε>0, has finite measure. The lower bound min(1,ε²)>0 proves this immediately by comparison of nonnegative integrals. This is the key finite-annulus ingredient for deriving sigma-finiteness of positive jump-magnitude Lévy measures from the standard truncated-square condition.
-- source:
--   Lévy integrability and pinned Mathlib lintegral_mono_ae, lintegral_mono_set, ENNReal.mul_lt_top_iff.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_levy_positive_tail_finite (μ : Measure ℝ) (ε : ℝ)
    (hε : 0 < ε)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    μ (Ici ε) < ⊤ := by sorry
