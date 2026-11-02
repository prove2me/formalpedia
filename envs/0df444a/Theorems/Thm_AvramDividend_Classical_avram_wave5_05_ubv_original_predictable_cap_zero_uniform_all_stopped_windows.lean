-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_stopped_windows
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_stopped_windows
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:28:32.791905+00:00
-- url     : https://prove2.me/theorems/4eb16341-486c-463d-9bcd-d1ad001d7da6
-- title:
--   Original UBV predictable cap-supported generator densities have zero mass on every path-dependent stopped window simultaneously
-- statement:
--   For actual capped controlled spectrally negative unbounded-variation Levy source, on a single original-process full-P event and a fixed SFinite atomless physical-time clock μ, EVERY path-dependent window of times [σ(ω),τ(ω)] and every nonnegative possibly infinite generator characteristic weight selected after ω has zero μ-lintegral on exact positive pre-ruin predictable cap contact within that window. No stopping-time hypothesis is necessary for this pathwise measure-zero restriction, so it applies in particular to arbitrary original controlled stopping/localisation windows and repeated cap contacts, including σ=0 and initial capital x=c. The result does not permanently stop at first cap and does not assert any boundary-local-time or singular dividend Stieltjes nullity.
-- source:
--   Proved single-event all-weights predictable cap-nullity 35fd2e0a-aab2-4685-8bce-b53aa9dbdd00; original controlled source and corrected canonical UBV core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_characteristic_weights

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_stopped_windows
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ (σ τ : Ω → ℝ≥0)
      (weight : ℝ≥0 → Ω → ℝ≥0∞),
      (∫⁻ t : ℝ≥0,
        if (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
              Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c) ∧
              (σ ω ≤ t ∧ t ≤ τ ω)
        then weight t ω else 0 ∂μ) = 0 := by sorry
