-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_04_original_BV_postright_terminal_drift_ceiling_ae
-- name    : AvramDividend.Classical.avram_wave7_04_original_BV_postright_terminal_drift_ceiling_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:51:40.130243+00:00
-- url     : https://prove2.me/theorems/88e28359-997d-4233-b6fa-b571e78d609e
-- title:
--   Original BV source post-rightpayment stopped-terminal reserve bounded above by deterministic drift ceiling
-- statement:
--   For the genuine spectrally negative BV Levy source, the controlled post-rightpayment surplus at any deterministic nonnegative clock is bounded almost surely by its initial capital plus physical BV drift times the clock, provided the initial right payment is nonnegative. This yields the exact finite interval needed to bound the surviving HJB terminal value for an infinite dividend cap.
-- source:
--   A source-faithful corollary of Proved W7-02 original BV controlled postpayment increment drift envelope 6c45ed32-71ad-4525-98ae-fa03ae0f0d8c at s=0, plus the original field X.X_zero and nonnegative initial right payment. This is a genuine a.e. bound on original X and D with no surrogate path law. It supports terminal L1 localisation for the Open W7-04 stopped Ito supermartingale 0618723a-bb0b-4fa0-94bc-4def7af7aafa.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_04_original_BV_postright_terminal_drift_ceiling_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hInitial : ∀ ω, 0 ≤ rightLimit D 0 ω)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      x + X.X T ω - rightLimit D T ω ≤
        x + (T : ℝ) * X.drift := by sorry
