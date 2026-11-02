-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_strict_subcap_ae_all_countable_atomless_clocks
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_strict_subcap_ae_all_countable_atomless_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:46:45.709789+00:00
-- url     : https://prove2.me/theorems/e893a975-5297-4018-9444-7cac36447394
-- title:
--   One original UBV event places true predictable reserve strictly below cap at almost every positive surviving time on every countable atomless clock
-- statement:
--   For the original capped controlled spectrally negative UBV Levy reserve, under a prescribed countable family of fixed s-finite atomless time clocks μ_n, there is one P-conull event on which for every n the actual predictable pre-event reserve leftLim(x+X−rightLimit D) lies strictly below c at μ_n-almost every positive time before ruin. The process may start at cap and revisit it; no first-cap permanent stopping or every-dividend-interior hypothesis is made. This gives one source-faithful clock-independent cap boundary premise for Gaussian and jump-compensator generator terms, without implying the vanishing of singular local time or Stieltjes dividends.
-- source:
--   Parent direct predictable strict-subcap μ-a.e target avram_wave5_05_ubv_original_predictable_strict_subcap_ae_on_atomless_clock, publication request c0564d70-503d-4ccc-9c25-21248dd09889, prove parent before publication. Corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_strict_subcap_ae_on_atomless_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_strict_subcap_ae_all_countable_atomless_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : ℕ → Measure ℝ≥0)
    (hsf : ∀ n, SFinite (μ n))
    (hatom : ∀ n, NullSingletonClass (μ n)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ t : ℝ≥0 ∂μ n,
      0 < t → (t : ℝ≥0∞) < ruinTime X x D ω →
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t < c := by sorry
