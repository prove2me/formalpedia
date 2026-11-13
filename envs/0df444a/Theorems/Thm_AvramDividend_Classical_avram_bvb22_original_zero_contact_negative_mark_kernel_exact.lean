-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_contact_negative_mark_kernel_exact
-- name    : AvramDividend.Classical.avram_bvb22_original_zero_contact_negative_mark_kernel_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:55:41.93601+00:00
-- url     : https://prove2.me/theorems/14335b0d-677d-45d6-aa50-cbbbe553c387
-- title:
--   Original BV negative-mark jump kernel at zero reserve equals negative intensity times initial reward
-- statement:
--   For the original finite-negative-activity Levy source and any candidate that vanishes strictly below zero, the signed negative-mark generator kernel at physical zero reserve is exactly minus the zero-reserve value times negative-jump intensity. This term survives on zero-contact paths even though open-interior grid masks vanish. The identity is suitable for retaining the lost contact compensator in source-exact BV cash proofs.
-- source:
--   Original SpectrallyNegativeLevy negative mark measure; explicit zero reserve computation and Avram-Palmowski-Pistorius (2007) Proposition 4(i), eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb22_original_zero_contact_negative_mark_kernel_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw_neg : ∀ z < 0, w z = 0)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν) =
      -(w 0) * (X.ν (Iio (0 : ℝ))).toReal := by sorry
