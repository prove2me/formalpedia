-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_piecewise_terminal_w_uniform_bound
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_piecewise_terminal_w_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:55:36.98159+00:00
-- url     : https://prove2.me/theorems/da9dc906-20bd-4a5b-b4a3-7e130003011a
-- title:
--   Finite-cap bound for the original piecewise stopped postpayment value
-- statement:
--   If the capital cap is finite, half-line continuity and zero-below-zero boundary data uniformly bound w at the actual piecewise stopped post-right-payment reserve, including the ruin alternative and an initial payment at time zero. This supplies a source-exact finite-cap localisation/UI bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_piecewise_terminal_w_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (σ ω) ω - rightLimit D (σ ω) ω
      else riskProcess X x D (σ ω) ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ω, |w (W ω)| ≤ B := by sorry
