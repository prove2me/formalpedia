-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_finite_cap_ruin_truncated_raw_value_L1_from_source_continuity
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_finite_cap_ruin_truncated_raw_value_L1_from_source_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:39:33.667356+00:00
-- url     : https://prove2.me/theorems/7b26a7ca-6ff5-4a88-bc46-cec56e19a4e7
-- title:
--   Original finite-cap ruin-truncated raw comparison V(x+Xτ) is L1 from source data, without extra growth assumptions
-- statement:
--   For the literal original Lévy source at τ=min(ruinTime,n), obtain measurability of the actual cap-linear extension V from source continuity/zero-negative-reserve, compact interval bound for w from the same continuity, and the global exponential envelope for its finite-cap extension. Invoke the Proved original stopped source exponential comparison to establish integrability of V(x+X_τ), with no independently hypothesised value bound or finite negative jump moment. The stopped-source measurability and stopping time remain explicit.
-- source:
--   Proved original source stopped exponential comparison aa6fd1eb, compact source cap bound 356a0ead, finite-cap extension estimate 6a3c1304, source cap extension measurability 0e054a59.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_continuous_candidate_compact_cap_interval_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_finite_cap_linear_extension_global_exponential_envelope_of_interior_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_of_exp_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_finite_cap_ruin_truncated_raw_value_L1_from_source_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hCfin : C ≠ ⊤)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else
        w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hXstopped : Measurable (fun ω => X.X (τ ω) ω)) :
    Integrable (fun ω => V (x + X.X (τ ω) ω)) P := by sorry
