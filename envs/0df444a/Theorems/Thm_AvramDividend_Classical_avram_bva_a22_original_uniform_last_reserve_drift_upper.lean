-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_uniform_last_reserve_drift_upper
-- name    : AvramDividend.Classical.avram_bva_a22_original_uniform_last_reserve_drift_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:58:45.679542+00:00
-- url     : https://prove2.me/theorems/6f23a15d-cc6b-40e6-b24d-3775dec936f3
-- title:
--   Original BV controlled reserve cannot rise by more than physical positive drift over the exact last uniform mesh interval, for all paths almost surely
-- statement:
--   For the genuine original bounded-variation spectrally negative Lévy X and the actual dividend strategy D, on one full original probability event for every physical uniform-grid row the increase of the original post-rightpayment controlled reserve between its last strict grid clock and the exact full horizon T is at most T/(m+2) times the positive part of the physical Lévy drift. This bound is source-exact and requires no lower reserve compact mask, no candidate differentiability or finite negative-jump activity. It is the sharper geometric input for the noncompact-boundary terminal C1 error, since arbitrarily large negative source jumps cannot cause a positive reserve increment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_uniform_last_reserve_drift_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∀ᵐ ω ∂P, ∀ m : ℕ,
      (x + X.X S ω - rightLimit D S ω) -
        (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) ≤
        (T / ((m : ℝ) + 2)) * max X.drift 0 := by sorry
