-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_stieltjes10_original_all_grid_prepayment_with_initial_correction
-- name    : AvramDividend.Classical.avram_bv_stieltjes10_original_all_grid_prepayment_with_initial_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:41:31.434237+00:00
-- url     : https://prove2.me/theorems/e1a080b5-cc4e-4eca-87c6-6fb87d99b49d
-- title:
--   Original prepayment reserve at every grid node with exact zero-time dividend correction
-- statement:
--   For every original dividend strategy and arbitrary countable deterministic sampling grid (including zero), identify a single probability-one event on which all positive grid samples equal the original prepayment reserve, and the zero sample differs by the exact right-dividend atom. This is the direct reserve-Z bridge for original physical-cell budgets and uses no martingale construction.
-- source:
--   Proved original positive countable grid prestate e26f2e74 plus pinned Mathlib leftLim_eq_of_isBot at zero and original riskProcess/X_zero. Explicit time-zero correction must not vanish.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_stieltjes10_original_countable_positive_grid_prejump
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_stieltjes10_original_all_grid_prepayment_with_initial_correction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ n,
      Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n) =
        riskProcess X x D (u n) ω -
          (if u n = 0 then rightLimit D 0 ω - D 0 ω else 0) := by sorry
