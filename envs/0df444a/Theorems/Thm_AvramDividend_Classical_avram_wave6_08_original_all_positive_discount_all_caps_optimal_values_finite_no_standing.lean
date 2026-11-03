-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_all_positive_discount_all_caps_optimal_values_finite_no_standing
-- name    : AvramDividend.Classical.avram_wave6_08_original_all_positive_discount_all_caps_optimal_values_finite_no_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:08:17.417972+00:00
-- url     : https://prove2.me/theorems/473e37b4-a129-433a-9213-5855f9ec3cfa
-- title:
--   Any spectrally negative original Lévy has finite all-cap and unrestricted dividend values at every positive discount, without Standing
-- statement:
--   For every original spectrally negative Lévy process, x and q>0, the optimal dividend value under every cap and the unrestricted optimum are genuinely finite ENNReal values. Source continuity supplies θ>0 with ψθ<q, then the Proved original θ all-cap value finiteness theorem applies.
-- source:
--   Genuine original ψ positive small tilt 6b7f5580 and source all-cap/unrestricted optimal value finiteness at q≥ψθ a9e292b2. Distinct unconditional positive-q result removes Standing, supports actual value-function finiteness in corrected UBV mission.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_theta_all_cap_and_unrestricted_optimal_value_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_all_positive_discount_all_caps_optimal_values_finite_no_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 < q) :
    (∀ C : ℝ≥0∞, valueFunctionLe X q C x < ⊤) ∧
      valueFunction X q x < ⊤ := by sorry
