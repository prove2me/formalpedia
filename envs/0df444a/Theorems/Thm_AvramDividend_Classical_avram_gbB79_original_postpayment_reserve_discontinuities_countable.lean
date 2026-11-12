-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB79_original_postpayment_reserve_discontinuities_countable
-- name    : AvramDividend.Classical.avram_gbB79_original_postpayment_reserve_discontinuities_countable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:21:45.765191+00:00
-- url     : https://prove2.me/theorems/063d063d-6dc7-420c-914f-020eb3d2fe38
-- title:
--   Original Gaussian Levy postpayment reserve has countably many discontinuities on continuous source paths
-- statement:
--   For the unchanged original spectrally negative Levy process X, original admissible dividend strategy D and original probability space, a sample path of the physical postpayment reserve x + X.X t omega - rightLimit D t omega has only countably many discontinuities whenever the original X sample path is continuous. This imports the source-specific B78 dividend right-limit discontinuity theorem and is a strict prerequisite for B61's a.e. left-grid coefficient convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB78_original_dividend_rightLimit_discontinuities_countable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB79_original_postpayment_reserve_discontinuities_countable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (ω : Ω)
    (hX : Continuous (fun s : ℝ≥0 => X.X s ω)) :
    Set.Countable {t : ℝ≥0 |
      ¬ ContinuousAt (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t} := by sorry
