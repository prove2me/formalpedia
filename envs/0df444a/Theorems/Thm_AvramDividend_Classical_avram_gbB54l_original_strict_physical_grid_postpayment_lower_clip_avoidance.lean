-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54l_original_strict_physical_grid_postpayment_lower_clip_avoidance
-- name    : AvramDividend.Classical.avram_gbB54l_original_strict_physical_grid_postpayment_lower_clip_avoidance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:35:36.156133+00:00
-- url     : https://prove2.me/theorems/874008c9-802c-4000-ba81-5abaf22ab31d
-- title:
--   Original Gaussian B54 physical mesh cannot visit the lower derivative clipping point before stopping
-- statement:
--   Under the original strictly positive stopped prepayment reserve floor delta, every physically sampled source postpayment reserve at a starting mesh time strictly before rho stays at least delta/2, including the mesh at t=0. Thus the lower clipped payoff kink is avoided by all source active Gaussian cells, without replacing original dividends by a Brownian companion. This is the exact lower-band source support needed in B54c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_gbB54l_original_strict_physical_grid_postpayment_lower_clip_avoidance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n m : ℕ) (ρ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ ω (i : ℕ), (i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) < ρ ω →
      δ / 2 ≤ x + X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) ω -
        rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) ω := by sorry
