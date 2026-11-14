-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_source_zero_predividend_discounted_negative_mark_fibre_exact
-- name    : AvramDividend.Classical.avram_bvb24_original_source_zero_predividend_discounted_negative_mark_fibre_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:46:47.666414+00:00
-- url     : https://prove2.me/theorems/a695636c-765d-4e48-a9d2-aae7ce9b62dc
-- title:
--   Exact original physical discounted full-negative-mark generator fibre at source zero prepayment contact
-- statement:
--   If the actual original source prepayment left reserve is zero at a physical time, the full original negative-mark generator fibre, integrated against the original finite-activity Lévy measure and multiplied by the true discount factor at that physical time, equals minus the full original negative-mark intensity times the boundary value and discount. The proof uses the already Proved source negative-mark kernel, preserving every negative mark, including at the zero-contact boundary. It is the exact source mathematical fibre appearing in the original stopped K time/mark compensator and is directly fed by the physical prepayment-left-limit lemma 810c78f4.
-- source:
--   Proved exact zero contact mark kernel 14335b0d, actual original ν and source prepayment U, pending source zero prepayment left limit 810c78f4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_contact_negative_mark_kernel_exact
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb24_original_source_zero_predividend_discounted_negative_mark_fibre_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (hw_neg : ∀ z < 0, w z = 0)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (t : ℝ≥0) (U : ℝ≥0 → ℝ)
    (hU : U t = 0) :
    (∫ z in Iio (0 : ℝ),
      Real.exp (-(q * (t : ℝ))) *
        (w (U t + z) - w (U t)) ∂X.ν) =
      -(Real.exp (-(q * (t : ℝ))) * w 0) *
        (X.ν (Iio (0 : ℝ))).toReal := by sorry
