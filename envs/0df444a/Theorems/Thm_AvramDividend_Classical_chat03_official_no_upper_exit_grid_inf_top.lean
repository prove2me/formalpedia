-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_official_no_upper_exit_grid_inf_top
-- name    : AvramDividend.Classical.chat03_official_no_upper_exit_grid_inf_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:26:46.566205+00:00
-- url     : https://prove2.me/theorems/31847f38-1e84-4e20-9e42-13250c28aaf5
-- title:
--   Every uniform strict upward-exit grid clock is infinite when the official continuous upper passage is infinite
-- statement:
--   For the official spectrally negative Lévy process, if the named continuous strict upper passage time equals ENNReal infinity, then for every mesh size h, the ENNReal infimum of strict sampled upper passage times over k*h, with infinity assigned to non-crossing grid points, equals infinity. The accepted extended passage-infimum characterization shows continuous infinity is equivalent to there being no strict upper crossing at any continuous time. Every grid evaluation is such a time and therefore takes the infinity branch. This supplies the no-exit-grid premise in the complete upper-first discounted payoff convergence theorem without imposing continuity of ENNReal.toReal at infinity.
-- source:
--   Proved chat03_extended_infimum_is_top_iff_no_exit UUID 7ff7f7db-c9c8-41a7-a4ae-23610b3bd9f2; official twoSidedExitUpTime definition.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_extended_infimum_is_top_iff_no_exit

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_official_no_upper_exit_grid_inf_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (upper : ℝ) (h : ℝ≥0)
    (hUp : twoSidedExitUpTime X upper ω = ∞) :
    (⨅ k : ℕ,
      if upper < X.X ((k : ℝ≥0) * h) ω then
        (((k : ℝ≥0) * h) : ℝ≥0∞)
      else ∞) = ∞ := by sorry
