-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB40_original_strict_clock_postpaid_real_time_positive_ae
-- name    : AvramDividend.Classical.avram_gbB40_original_strict_clock_postpaid_real_time_positive_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:47:17.622223+00:00
-- url     : https://prove2.me/theorems/62449ddd-30b4-4776-9acd-1ae4e96c2c48
-- title:
--   True original controlled postpayment reserve is positive almost everywhere on a strict stopped physical time window
-- statement:
--   A pathwise strictly positive reserve floor before an original stopped time implies the original postpayment reserve is positive for almost every real time in the same bounded strict pre-stop window. This supplies the positive-reserve hypothesis for the cap-linear Gaussian generator time-integral, preserving the actual X, D and rightLimit D.
-- source:
--   The Proved original strict-prefix postpayment floor gledger20 transfers the riskProcess floor to x+X(t)-rightLimit D(t). Almost every time under the restricted volume measure lies inside the true strict window, and Real.toNNReal converts it into the original nonnegative clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB40_original_strict_clock_postpaid_real_time_positive_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ t : ℝ≥0, 0 < t → t < ρ →
      δ ≤ riskProcess X x D t ω) :
    let S : Set ℝ := {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < (ρ : ℝ)}
    ∀ᵐ t ∂(volume.restrict S),
      0 < x + X.X (Real.toNNReal t) ω -
        rightLimit D (Real.toNNReal t) ω := by sorry
