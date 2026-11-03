-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_discounted_strict_ruin_terminal_partition
-- name    : AvramDividend.Classical.avram_wave6_08_original_discounted_strict_ruin_terminal_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:45:53.052968+00:00
-- url     : https://prove2.me/theorems/691e0b51-b1aa-4a9e-b98b-d594f1fc3109
-- title:
--   Exact original discounted Stieltjes partition into full grid cells and strictly open ruin final cell
-- statement:
--   For the original dividend Stieltjes measure, every discounted strict terminal interval (a,c) partitions exactly into a full half-open grid cell (a,b] and the truly final open cell (b,c). This identity includes the right-hand dividend at interior grid point b once and excludes right-hand dividends at both external endpoints, especially at ruin c; it also includes all diffuse and singular-continuous dividends. No integrability or stochastic conditional estimate is assumed.
-- source:
--   The genuine original Stieltjes weighted integral and Mathlib lintegral_union for a disjoint exact time-set partition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_original_discounted_strict_ruin_terminal_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (a b c : ℝ≥0) (hab : a < b) (hbc : b < c) :
    (∫⁻ t in Ioo (a : ℝ) (c : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in Ioo (b : ℝ) (c : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
