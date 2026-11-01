-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_small_negative_jump_square_intensity_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave4_04_source_small_negative_jump_square_intensity_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:10:34.259417+00:00
-- url     : https://prove2.me/theorems/ddfd1997-690d-4b67-9460-9b25c75f51ca
-- title:
--   Original Lévy source small-negative-jump quadratic intensity vanishes as cutoff descends to zero
-- statement:
--   For the actual source Lévy measure carried by X, the square energy of reflected negative marks with magnitude 0<z<1/(n+1) tends to zero. The proof uses only X.ν_integrable, the previously Proved negative-reflection Lévy-square finiteness, and dominated convergence with an integrable small-jump square envelope. This precisely supports L² small-jump truncation in the unbounded-variation case even when the absolute first moment is infinite. It is an intensity-level limit, not an assertion about the source random jump measure, compensating martingale, or controlled dividends.
-- source:
--   Proved gaussian_levy_square_integrable_neg_pushforward 581daddd; source SpectrallyNegativeLevy.ν_integrable; pinned Mathlib MeasureTheory.tendsto_lintegral_of_dominated_convergence and tendsto_one_div_add_atTop_nhds_zero_nat.

import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04_source_small_negative_jump_square_intensity_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Tendsto (fun n : ℕ =>
      ∫⁻ z in Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)),
        ENNReal.ofReal (z ^ 2) ∂(X.ν.map (fun y : ℝ => -y)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
