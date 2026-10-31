-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_zero_barrierSupValue_finite
-- name    : AvramDividend.Classical.avram_root29_05_zero_barrierSupValue_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:43:24.806236+00:00
-- url     : https://prove2.me/theorems/24b6bad6-2f4e-4842-bb4b-d5fe626e03cf
-- title:
--   Actual reflected-regulator zero-barrier dividend value is finite
-- statement:
--   For a Standing spectrally negative Lévy process at positive discount, the genuine killed-regulator zero-barrier expected dividend is finite given a genuine source scale function.
-- source:
--   Accepted true reflected zero-barrier identity b83a725b equates the exact barrierSupValue to ofReal of the finite real barrierValue W 0 0. ENNReal.ofReal_lt_top completes.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_eq_barrierValue

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_05_zero_barrierSupValue_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    barrierSupValue X 0 q < ∞ := by sorry
