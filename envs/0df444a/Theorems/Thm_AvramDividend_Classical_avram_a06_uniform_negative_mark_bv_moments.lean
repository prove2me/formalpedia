-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_bv_moments
-- name    : AvramDividend.Classical.avram_a06_uniform_negative_mark_bv_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T16:50:20.689466+00:00
-- url     : https://prove2.me/theorems/51e4a4b3-85f7-4f38-aa0d-b7cf44fc2fc2
-- title:
--   Compact uniform negative jumps have finite quadratic Lévy moment and small-jump variation
-- statement:
--   For the concrete bounded negative uniform jump law, simultaneously verify the Lévy-measure quadratic integrability and the bounded-variation small-jump absolute moment by domination with the constant one on its support. Both exact fields are needed when building the original finite-activity Avram source.
-- source:
--   Root-connected A06 source 115c3b1e: explicit compact negative jump law integrability certificate.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_uniform_negative_mark_bv_moments :
    (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2))
      ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) < ⊤ ∧
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y|
      ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) < ⊤ := by sorry
