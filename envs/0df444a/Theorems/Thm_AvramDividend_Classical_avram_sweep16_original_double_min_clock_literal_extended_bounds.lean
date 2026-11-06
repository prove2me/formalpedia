-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_literal_extended_bounds
-- name    : AvramDividend.Classical.avram_sweep16_original_double_min_clock_literal_extended_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:20:07.731118+00:00
-- url     : https://prove2.me/theorems/aceb77c2-2c47-404e-8222-358822cf9497
-- title:
--   Original natural ruin and local stopping double-min clock is finite with literal NNReal embedding and exact ruin/horizon bounds
-- statement:
--   At every sample and index for the unchanged original physical controlled Levy ruinTime, the doubly stopped extended clock min(min(ruinTime,n),S_k) lies below finite n, hence is never top. Its NNReal conversion coerced back to extended nonnegative time is literally identical, so it is at most the original ruin time and n. This is the source-exact clock arithmetic needed by localized stopped Ito estimates; it imposes no fictitious process identity or martingale claim.
-- source:
--   Original controlled dividend ruinTime, exact n truncation and physical localiser S. Uses only ENNReal coe_toNNReal and lattice order.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_original_double_min_clock_literal_extended_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (S : ℕ → Ω → ℝ≥0∞) :
    ∀ k ω,
      (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal :
        ℝ≥0∞) = min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)) ∧
      (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal :
        ℝ≥0∞) ≤ ruinTime X x D ω) ∧
      (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal :
        ℝ≥0∞) ≤ (n : ℝ≥0∞)) := by sorry
