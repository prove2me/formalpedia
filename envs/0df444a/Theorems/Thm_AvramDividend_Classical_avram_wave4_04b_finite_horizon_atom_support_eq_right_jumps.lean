-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_atom_support_eq_right_jumps
-- name    : AvramDividend.Classical.avram_wave4_04b_finite_horizon_atom_support_eq_right_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:41:53.372979+00:00
-- url     : https://prove2.me/theorems/0f17d656-7a50-49ed-a4b7-6dbdee7d33e4
-- title:
--   Exact support of the closed-horizon Stieltjes dividend atoms is the set of positive right-payment jumps
-- statement:
--   The exact nonzero singleton support of the actual Avram Stieltjes dividend measure restricted to the closed finite horizon [0,T] consists precisely of real payment times inside the interval at which the adapted cumulative dividend path has a strictly positive chronological right jump. This includes the initial payment atom at 0 and the terminal atom at T, and excludes all negative times and all times beyond T. The theorem does not assert that the complementary diffuse measure vanishes: singular-continuous dividend variation remains possible.
-- source:
--   Original dividendMeasure singleton identity plus restriction to [0,T], without an atomic concentration assumption. Supports the exact atomic summand in the full discounted dividend reward.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04b_finite_horizon_atom_support_eq_right_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    {s : ℝ | μ {s} ≠ 0} =
      {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
        0 < rightLimit D s.toNNReal ω - D s.toNNReal ω} := by sorry
