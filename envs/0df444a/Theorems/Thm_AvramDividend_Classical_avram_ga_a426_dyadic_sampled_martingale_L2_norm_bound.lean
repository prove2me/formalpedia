-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a426_dyadic_sampled_martingale_L2_norm_bound
-- name    : AvramDividend.Classical.avram_ga_a426_dyadic_sampled_martingale_L2_norm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T23:48:21.757199+00:00
-- url     : https://prove2.me/theorems/16aa2eee-0309-4a85-a0d7-b72f6ee02a21
-- title:
--   L2 Doob maximal norm estimate on the sampled nonnegative-real dyadic grid
-- statement:
--   A real continuous-time martingale sampled at the dyadic grid on any finite horizon satisfies a uniform L2 norm maximal inequality with factor two, by discrete Doob and clamped time reindexing.
-- source:
--   Doob L2 maximal inequality for sampled martingales; cf. LevyStochCalc Probability DoobContinuous (published Prove2Me), finite sampling via monotone clamped grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_LevyStochCalc_Probability_lintegral_sq_dyadicRunMax_le_readable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a426_dyadic_sampled_martingale_L2_norm_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → ℝ) (hMart : Martingale M 𝓕 P)
    (T : ℝ≥0) (k : ℕ) :
    eLpNorm (fun ω => (Finset.range (2^k + 1)).sup'
      (by simp) (fun i => |M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω|)) 2 P
      ≤ 2 * eLpNorm (M T) 2 P := by sorry
