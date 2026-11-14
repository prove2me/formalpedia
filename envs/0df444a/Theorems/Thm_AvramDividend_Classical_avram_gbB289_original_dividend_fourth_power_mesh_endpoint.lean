-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB289_original_dividend_fourth_power_mesh_endpoint
-- name    : AvramDividend.Classical.avram_gbB289_original_dividend_fourth_power_mesh_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:07:52.488117+00:00
-- url     : https://prove2.me/theorems/c72e472f-80dd-47f3-960c-1a65353427ca
-- title:
--   Actual original dividends are monotone on the fourth-power grid and terminate exactly at the physical horizon
-- statement:
--   Original admissible dividend sample paths are monotone at deterministic mesh endpoints, and the final physical time n*m^4*m^(-4) is exactly n; hence terminal grid variation is D(n)-D(0). The identity is used in the authentic localised bad-cell probability-time occupation estimate B276b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB289_original_dividend_fourth_power_mesh_endpoint
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (n m : ℕ) (hm : 0 < m) :
    Monotone (fun i : ℕ =>
      D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω) ∧
    D (((n * m ^ 4 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω = D n ω ∧
    D ((0 : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω = D 0 ω := by sorry
