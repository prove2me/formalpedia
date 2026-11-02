-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_prejump_caplinear_source_generator_eq_ae
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_prejump_caplinear_source_generator_eq_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:37:29.958857+00:00
-- url     : https://prove2.me/theorems/6ca089c4-c02e-4b12-9a59-7dfb5de4b922
-- title:
--   Same-original-source cap-linear continuation preserves the Lévy generator at genuine predictable pre-event UBV reserves at atomless-clock a.e. surviving time
-- statement:
--   For a positive finite cap c and an actual same-source unbounded-variation admissible controlled dividend strategy, the compensated source Levy generator applied to the slope-one continuation v_c(y)=w(y) below c and w(c)+y−c above c agrees with the source generator applied to w itself at the true chronological pre-event reserve, at almost every positive pre-ruin time against any atomless s-finite physical-time clock. The true predictable state is strictly below c almost everywhere even if the process starts at c and makes dividends at c. This exact generator equality requires no differentiability at the cap, no generator integrability at cap contact and no first-contact stopping.
-- source:
--   Accepted original predictable strict interior c9db7a94-e185-4483-b0d9-b79a2d3a7487 and Proved slope-one source generator equality de1c1aee-43d3-47a2-83ae-6115b56249e3. Corrected canonical UBV core 429e17ca-5528-40b5-b593-7c03973d0706 untouched.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generator_eq_interior

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_prejump_caplinear_source_generator_eq_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
        X.generator (fun y => if y ≤ c then w y else w c + (y - c))
          (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) =
        X.generator w
          (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) := by sorry
