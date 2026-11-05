-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_real_truncated_ruin_nnreal_stopping
-- name    : AvramDividend.Classical.avram_p3_bv_original_real_truncated_ruin_nnreal_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:45:30.79355+00:00
-- url     : https://prove2.me/theorems/712c7638-64fd-4d49-9354-bf8546a999a1
-- title:
--   Original controlled BV ruin time truncation at arbitrary nonnegative real horizon is a bounded stopping time
-- statement:
--   For every nonnegative real T, the original dividend-controlled ruin time truncated at T and converted from ENNReal to NNReal is bounded by T and is a stopping time for the original right-continuous filtration. In particular the integrable stopped-jump P2 bridge applies at the exact real horizon needed for finite-horizon P3 verification.
-- source:
--   Original genuine ruinTime right-continuous stopping theorem 2d036d4f and the original accepted integer-horizon bound and eventwise min stopping proof 99c02ca9 and 7bcaac6d; generalises the exact source argument to T : ℝ≥0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_real_truncated_ruin_nnreal_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    (∀ ω, τ ω ≤ T) ∧
      IsStoppingTime 𝓕.rightCont
        (fun ω => (τ ω : WithTop ℝ≥0)) := by sorry
