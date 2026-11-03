-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_dividend_full_mesh_mass_error_vanish
-- name    : AvramDividend.Classical.avram_wave6_08_original_dividend_full_mesh_mass_error_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:51:52.164941+00:00
-- url     : https://prove2.me/theorems/840339b5-1b4d-4a4f-a060-17d2997bdbbf
-- title:
--   Actual original dividend full-Stieltjes finite-time mesh error vanishes with no extra path-mass assumption
-- statement:
--   For the actual dividendMeasure of any adapted admissible monotone right-limit strategy, its complete Stieltjes mass on a bounded horizon is finite and equal to the right-limit dividend increment. Thus for q≥0 and any nonnegative real mesh widths tending to zero, the real-valued product q times mesh width times that entire mass tends to zero pathwise. Applies uniformly to diffuse, singular-continuous and countable right-atomic dividend payments; no extra boundedness or missing stochastic compensation condition is assumed.
-- source:
--   Proved source dividendMeasure_Ioc_rightLimit and dividendStrategy_rightLimit_monotone, using ENNReal.toReal_mul and elementary convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave6_08_original_dividend_full_mesh_mass_error_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (mesh : ℕ → ℝ) (hmesh : ∀ n, 0 ≤ mesh n)
    (hmesh0 : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun n =>
      (ENNReal.ofReal (q * mesh n) *
        dividendMeasure D ω (Ioc (0 : ℝ) (T : ℝ))).toReal)
      atTop (𝓝 0) := by sorry
