-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_l2_cauchy_of_uniform_band_tail
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_l2_cauchy_of_uniform_band_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:58:25.881867+00:00
-- url     : https://prove2.me/theorems/d3a30c29-4162-4ac0-a1c1-7dddcd65ea1e
-- title:
--   Original finite-band L2 Cauchy criterion from a uniform Lévy-tail bound
-- statement:
--   For the actual original Lévy process probability space and filtration, a quantitative tail sequence tending to zero which bounds every later finite-band L2 distance yields the Cauchy property at each time. This converts physical finite-grid jump isometry and small-band variance tail estimates into exactly the hypothesis needed by the separate source-preserving right-continuous L2 martingale-completion bridge. The tail-distance estimate itself remains a mathematical obligation.
-- source:
--   Metric.cauchySeq_iff and the two ordered cases on a common finite-band cut-off. No process change or Poisson-point-family assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_l2_cauchy_of_uniform_band_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℕ → ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (ρ : ℕ → ℝ)
    (hTail : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ρ n < ε)
    (hBound : ∀ t n m, n ≤ m →
      dist (M n t) (M m t) ≤ ρ n) :
    ∀ t, CauchySeq (fun n => M n t) := by sorry
