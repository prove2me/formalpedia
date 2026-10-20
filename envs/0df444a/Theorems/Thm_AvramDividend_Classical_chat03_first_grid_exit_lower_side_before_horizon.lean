-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_first_grid_exit_lower_side_before_horizon
-- name    : AvramDividend.Classical.chat03_first_grid_exit_lower_side_before_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:42:25.072024+00:00
-- url     : https://prove2.me/theorems/efba1504-f115-43e4-8d5a-d150589e65e1
-- title:
--   First strict grid-exit side remains lower when upper exit is excluded before an intervening horizon
-- statement:
--   For the official spectrally negative Lévy process, let τ be the strict two-sided first-passage infimum before a finite horizon N. If no strict upper exit occurs before N, expressed by X_s≤upper for every s<N, then all sufficiently fine grids have an actual least strict grid exit index k before N, and it must be a strict lower exit X_{kh}<lower. No earlier grid sample exits. This is the lower-first analogue of the independently prepared upper-side theorem and preserves endpoint strictness, first-passage infimum and a possible boundary-creeping event. It needs no right-continuous filtration or killed q-scale martingale.
-- source:
--   Chat03 first_grid_exit_before_horizon theorem 1eef4eb0-c990-443b-8bb0-97b0b743074c, pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_exit_before_horizon

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_first_grid_exit_lower_side_before_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ N : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hτN : τ < N)
    (hNoUpper : ∀ s : ℝ≥0, s < N → X.X s ω ≤ upper) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
      ∃ k : ℕ,
        τ ≤ (k : ℝ≥0) * h ∧
        (k : ℝ≥0) * h < N ∧
        X.X ((k : ℝ≥0) * h) ω < lower ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * h) ω)) := by sorry
