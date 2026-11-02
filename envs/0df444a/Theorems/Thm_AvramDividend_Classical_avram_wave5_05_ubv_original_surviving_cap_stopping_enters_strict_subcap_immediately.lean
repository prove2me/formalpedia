-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_surviving_cap_stopping_enters_strict_subcap_immediately
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_surviving_cap_stopping_enters_strict_subcap_immediately
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:10:29.388578+00:00
-- url     : https://prove2.me/theorems/24948d87-b6fb-4574-9536-29a711da94aa
-- title:
--   At every surviving finite cap-contact stopping time, the genuine original UBV controlled reserve re-enters below cap before ruin, arbitrarily soon
-- statement:
--   For genuine same-filtration unbounded-variation spectrally negative Levy dynamics X and nondecreasing adapted dividends D, suppose a finite filtration stopping time τ lies strictly before ruin and the actual controlled reserve is exactly at cap c there. Almost surely, for every arbitrarily short positive time window the actual controlled reserve has a strictly positive future time still before ruin and strictly below c. In particular it applies to τ≡0 when initial capital equals its cap and ruin has not already occurred; it never stops the process permanently on cap contact and does not assume that dividend payments are strictly interior.
-- source:
--   Accepted original-source finite stopping time downward regularity 66982d13-ea38-4a01-9f6c-49753efab1c0, accepted source proof aa42a21a-9b17-47b3-b72d-a6efd383ae5c for ENNReal ruin-time intermediate horizon, real original D monotonicity, and corrected core 429e17ca-5528-40b5-b593-7c03973d0706. Independent boundary regularity helper, no controlled Ito-Meyer assertion, no milestone change.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_levy_finite_stopping_downward_regular_no_grid

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_surviving_cap_stopping_enters_strict_subcap_immediately
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P,
      (τ ω : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D (τ ω) ω = c →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, 0 < s ∧ s < ε ∧
          ((τ ω + s : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω ∧
          riskProcess X x D (τ ω + s) ω < c := by sorry
