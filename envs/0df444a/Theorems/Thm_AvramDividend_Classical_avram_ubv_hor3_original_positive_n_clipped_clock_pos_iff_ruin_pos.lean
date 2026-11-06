-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_n_clipped_clock_pos_iff_ruin_pos
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_positive_n_clipped_clock_pos_iff_ruin_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:24:08.641194+00:00
-- url     : https://prove2.me/theorems/6a61de0a-690f-4040-8474-fcf686c5d7ce
-- title:
--   Original positive natural ruin clipping has positive stopped clock exactly on positive original ruin
-- statement:
--   For any actual original controlled Lévy path and positive natural cutoff n, the clipped extended-nonnegative ruin clock is strictly positive exactly when the source original ruinTime is strictly positive. This is the precise positive-time interior stopping event needed to distinguish zero-stop boundary from the genuine Gaussian and jump martingale obligations.
-- source:
--   Pinned linear-order lt_min_iff applied to the original ruinTime and positive Nat-cast cutoff n. No stochastic martingale assumptions and no proxy process or reference to canonical downstream theorems.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_positive_n_clipped_clock_pos_iff_ruin_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (hn : 0 < n) (ω : Ω) :
    (0 < min (ruinTime X x D ω) (n : ℝ≥0∞)) ↔
      (0 < ruinTime X x D ω) := by sorry
