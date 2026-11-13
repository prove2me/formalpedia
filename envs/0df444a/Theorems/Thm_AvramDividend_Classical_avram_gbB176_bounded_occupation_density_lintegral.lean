-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB176_bounded_occupation_density_lintegral
-- name    : AvramDividend.Classical.avram_gbB176_bounded_occupation_density_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:38:57.669396+00:00
-- url     : https://prove2.me/theorems/388fba5f-52f7-4c98-ae2d-9b7af853347b
-- title:
--   Bounded local-time density controls its restricted interval lintegral
-- statement:
--   A bounded nonnegative occupation density has interval integral at most the density supremum times Lebesgue interval mass. Used to transfer the stochastic local-time occupation identity to the original finite-cap Gaussian small-ball bound B174.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB176_bounded_occupation_density_lintegral
    (ℓ : ℝ → ℝ≥0∞) (B : ℝ≥0∞) (a b : ℝ)
    (hℓ : ∀ z, ℓ z ≤ B) :
    ∫⁻ z in Ioo a b, ℓ z ∂volume ≤
      B * volume (Ioo a b) := by sorry
