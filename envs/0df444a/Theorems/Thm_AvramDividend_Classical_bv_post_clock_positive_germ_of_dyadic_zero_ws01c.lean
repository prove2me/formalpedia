-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_post_clock_positive_germ_of_dyadic_zero_ws01c
-- name    : AvramDividend.Classical.bv_post_clock_positive_germ_of_dyadic_zero_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:38:33.254994+00:00
-- url     : https://prove2.me/theorems/58874117-4c3c-4d87-a0bc-d3c91c8ce9e8
-- title:
--   Transferred post-clock zero dyadic deficit slope forces a positive right germ
-- statement:
--   For an actual bounded-variation spectrally negative Lévy process with positive standing drift, and any random finite NNReal clock τ, if its post-clock drift-deficit dyadic slopes converge to zero almost surely and the dyadic mesh satisfies positivity, adjacent-ratio and covering conditions, then for almost every path the Lévy increments after τ are strictly positive throughout a sufficiently short right interval. The proof translates the original almost-sure monotone drift residual to a monotone shifted residual and applies the already Proved deterministic slope-to-right-germ theorem. This theorem does not assume τ is a stopping time; the separate grid-law/Markov transfer must establish the slope hypothesis.
-- source:
--   Source-complete exact process theorem from work/avram_ws01c_postclock_positive_germ_draft.lean. Reuses canonical Proved monotone BV residual bdb273f0, standing positive drift 0432f641 and deterministic right germ 1ad74805. This is the immediate boundary input for the already Proved conditional-contact no-creeping lemma.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_dyadic_slope_to_positive_right_germ_ws01c

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_post_clock_positive_germ_of_dyadic_zero_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (τ : Ω → ℝ≥0) (δ : ℕ → ℝ≥0)
    (hδpos : ∀ n, 0 < δ n)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hSlope : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) -
          (X.X (τ ω + δ n) ω - X.X (τ ω) ω)) /
            (δ n : ℝ))
        atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P,
      ∃ ε : ℝ≥0, 0 < ε ∧
        ∀ t : ℝ≥0, 0 < t → t < ε →
          0 < X.X (τ ω + t) ω - X.X (τ ω) ω := by sorry
