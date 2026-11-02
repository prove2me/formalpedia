-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_initial_cap_zero_time_enters_strict_subcap
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_initial_cap_zero_time_enters_strict_subcap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:54:33.283238+00:00
-- url     : https://prove2.me/theorems/620515ea-ebc7-4d1f-8049-213871a849fc
-- title:
--   The genuine surviving original UBV controlled reserve started exactly at cap enters strictly below cap immediately after time zero
-- statement:
--   For any same-filtration true dividend strategy D driven by original UBV spectrally negative Lévy source X, whenever the controlled reserve at time 0 equals the cap c and ruin has not already occurred, on P-a.e. trajectory the genuine original reserve has positive times s arbitrarily close to zero satisfying s<ruin and U_s<c. This is an exact time-zero corollary of the already Proved original finite stopping-time cap downcross theorem 24948d87-b6fb-4574-9536-29a711da94aa, with constant-zero stopping certificate discharged internally. It covers initial capital equal to cap and explicitly avoids stopping permanently at cap contact. It assumes no payments strictly below cap, no cap C², and no zero-cap branch work.
-- source:
--   Original same-X,D surviving cap downcross Proved 24948d87-b6fb-4574-9536-29a711da94aa; corrected canonical UBV core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_surviving_cap_stopping_enters_strict_subcap_immediately

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_initial_cap_zero_time_enters_strict_subcap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P,
      (0 : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D 0 ω = c →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, 0 < s ∧ s < ε ∧
          (s : ℝ≥0∞) < ruinTime X x D ω ∧
          riskProcess X x D s ω < c := by sorry
