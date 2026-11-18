-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_finitecap_caplinear_j_envelope_tendsto_zero
-- name    : AvramDividend.Classical.avram_ga_finitecap_caplinear_j_envelope_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:16:39.999396+00:00
-- url     : https://prove2.me/theorems/7e4e16eb-b8f6-498c-aad5-aab01d2d983f
-- title:
--   Original finite-cap caplinear upper-strip correction vanishes as clipping level tends to cap
-- statement:
--   For any strictly positive real cap C and w continuous on nonnegative reserves, the original Avram clipped caplinear upper-strip correction (w C - w b_j) - (C - b_j), with b_j=C*(j+1)/(j+2), tends to zero as j grows.

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ga_finitecap_caplinear_j_envelope_tendsto_zero
    (C : ℝ) (hC : 0 < C) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Set.Ici 0)) :
    Tendsto (fun j : ℕ =>
      (w C - w (C * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) -
        (C - C * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))))
      atTop (nhds (0 : ℝ)) := by sorry
