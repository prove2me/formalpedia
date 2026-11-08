-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord9_turn8_geometric_initial_reserve_admissible
-- name    : AvramDividend.Classical.avram_coord9_turn8_geometric_initial_reserve_admissible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T00:43:16.938832+00:00
-- url     : https://prove2.me/theorems/257c4336-6fe0-48b8-92b6-d82a1039f664
-- title:
--   Geometric initial reserve yields an original admissible infinite-cap step
-- statement:
--   For a genuine original spectrally negative Levy process, an adapted nonnegative marked post-payment reserve bounded by initial surplus produces an affordable random immediate dividend and a fully admissible infinite-cap strategy.
-- source:
--   Exact composition of three Proved original source lemmas for initial time-zero payout, right-limit and admissibility. A useful countermodel assumption bridge, no stochastic process or initial mark is constructed.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_coord9_turn8_random_zero_lump_dividend_strategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_rightlimit
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_step_admissible_infinite_cap_of_rightLimit
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A geometrically marked positive reserve gives an affordable, adapted
    immediate dividend and hence an exact original infinite-cap strategy. -/

theorem AvramDividend.Classical.avram_coord9_turn8_geometric_initial_reserve_admissible
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (K : Ω → ℕ) (y : ℕ → ℝ)
    (hy : ∀ k, 0 ≤ y k)
    (hyle : ∀ k, y k ≤ x)
    (hadapt : ∀ t : ℝ≥0, 0 < t →
      Measurable[𝓕 t] (fun ω : Ω => y (K ω))) :
    IsAdmissibleLe X x ⊤
      (fun t ω => if t = 0 then 0 else x - y (K ω)) := by sorry
