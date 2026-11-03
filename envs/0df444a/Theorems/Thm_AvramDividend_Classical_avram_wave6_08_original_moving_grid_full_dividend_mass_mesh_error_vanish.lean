-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_moving_grid_full_dividend_mass_mesh_error_vanish
-- name    : AvramDividend.Classical.avram_wave6_08_original_moving_grid_full_dividend_mass_mesh_error_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:57:45.293982+00:00
-- url     : https://prove2.me/theorems/19dce1c2-4f99-4c2a-b2ea-fee4f449d0b4
-- title:
--   Actual moving-grid full dividend-measure discount error vanishes without extra uniform variation premise
-- statement:
--   For any genuine original dividend strategy, nonnegative discount and a family of monotone chronological grids bounded by T, the exact real q times mesh times full Stieltjes dividendMeasure mass on each moving grid interval converges to zero when the nonnegative mesh widths tend to zero. The conclusion includes all countable payment atoms and singular-continuous variation and uses no new stochastic martingale estimate or assumed path-variation bound.
-- source:
--   Source right-limit measure mass identity and monotone strategy, with real squeeze theorem on the finite total dividend increment up to T.

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

theorem AvramDividend.Classical.avram_wave6_08_original_moving_grid_full_dividend_mass_mesh_error_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, Monotone (u n))
    (k : ℕ → ℕ) (hbound : ∀ n, u n (k n) ≤ T)
    (mesh : ℕ → ℝ) (hmesh : ∀ n, 0 ≤ mesh n)
    (hmesh0 : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun n =>
      (ENNReal.ofReal (q * mesh n) *
        dividendMeasure D ω
          (Ioc (u n 0 : ℝ) (u n (k n) : ℝ))).toReal)
      atTop (𝓝 0) := by sorry
