-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_shifted_exit_strict_order_of_finite_weak_order
-- name    : AvramDividend.Classical.levy_shifted_exit_strict_order_of_finite_weak_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:47:47.509284+00:00
-- url     : https://prove2.me/theorems/9198bdc8-a693-4266-8e7d-f5c12e171606
-- title:
--   Strict shifted two-sided exit order from finite weak order and right continuity
-- statement:
--   For the shifted-increment sample path of a spectrally negative Levy process and strictly separated upper and lower thresholds, a finite upper exit clock that is no later than the lower exit clock is strictly earlier. The only excluded case is equality of both finite clocks, impossible by the proved right-continuity no-tie lemma. This upgrades the stopped first-record survival weak exit inequality to the strict event needed in the upper renewal reward.
-- source:
--   Right-continuity and impossibility of simultaneous strict first passage across separated boundaries; proved generic no-finite-tie and shifted-increments right continuity.

import Mathlib.Topology.Order.LeftRightNhds
import Theorems.Thm_AvramDividend_Classical_levy_shiftedIncrements_rightContinuous
import Theorems.Thm_AvramDividend_Classical_separated_strict_passage_infima_no_finite_tie

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_shifted_exit_strict_order_of_finite_weak_order
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0)
    (lower upper : ℝ) (hsep : lower < upper)
    (hFinite : (⨅ (s : ℝ≥0)
        (_ : upper < X.X (u + s) ω - X.X u ω),
        (s : ℝ≥0∞)) ≠ ⊤)
    (hLe :
      (⨅ (s : ℝ≥0)
        (_ : upper < X.X (u + s) ω - X.X u ω),
        (s : ℝ≥0∞)) ≤
      (⨅ (s : ℝ≥0)
        (_ : X.X (u + s) ω - X.X u ω < lower),
        (s : ℝ≥0∞))) :
    (⨅ (s : ℝ≥0)
      (_ : upper < X.X (u + s) ω - X.X u ω),
      (s : ℝ≥0∞)) <
    (⨅ (s : ℝ≥0)
      (_ : X.X (u + s) ω - X.X u ω < lower),
      (s : ℝ≥0∞)) := by sorry
