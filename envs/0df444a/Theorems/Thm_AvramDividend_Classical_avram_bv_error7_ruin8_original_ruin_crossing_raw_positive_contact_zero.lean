-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_ruin_crossing_raw_positive_contact_zero
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_original_ruin_crossing_raw_positive_contact_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:11:32.166966+00:00
-- url     : https://prove2.me/theorems/c1f3944e-be2a-4f92-b740-a7cb1df3228a
-- title:
--   Original stopped BV ruin-crossing last cell has identically zero positive raw barrier-value error
-- statement:
--   For the authentic admissible dividend strategy and compensated stopped physical last cell, whenever the pre-contact reserve is nonnegative but the post-contact reserve crosses below zero, the positive part of the exact raw barrier-value change is identically zero. This handles ruin crossing separately from the nonnegative compact reserve continuity argument.
-- source:
--   Use Proved vcstar_eq_zero_of_neg 07dcf6e9 and Proved avram_sweep17_vcstar_nonnegative_without_smoothness 494b2f23 with original source-defined z and c. No BV prebudget, generator error nor assumed bounded derivative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_nonnegative_without_smoothness

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_original_ruin_crossing_raw_positive_contact_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (z c : ℕ → Ω → ℝ)
    (hzSource : ∀ m ω, z m ω =
      if k m ω = 0 then 0 else
        x + X.X (u m (k m ω - 1)) ω -
          rightLimit D (u m (k m ω - 1)) ω)
    (hcSource : ∀ m ω, c m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       if k m ω = 0 then 0 else
         Y (u m (k m ω)) - Y (u m (k m ω - 1))))
    (Err : ℕ → Ω → ℝ)
    (hErrSource : ∀ m ω, Err m ω =
      vcstar W (z m ω + c m ω) - vcstar W (z m ω)) :
    ∀ m ω, 0 ≤ z m ω → z m ω + c m ω < 0 →
      max (Err m ω) 0 = 0:= by sorry
