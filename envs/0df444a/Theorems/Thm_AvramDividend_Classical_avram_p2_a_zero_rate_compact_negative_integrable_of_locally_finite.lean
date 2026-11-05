-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_integrable_of_locally_finite
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_compact_negative_integrable_of_locally_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:58:14.856264+00:00
-- url     : https://prove2.me/theorems/cc4aa5a2-ebc7-49a6-96f6-73afa33dece2
-- title:
--   All original compact-negative tests are integrable under finite separated-band intensity
-- statement:
--   A Borel measure whose mass is finite on every negative halfline separated from zero integrates every continuous real test compactly supported strictly within the negative reals. Extract the original P2-A support band and apply the Proved P2-G finite-negative-band Bochner integrability theorem. This supplies the exact integrability hypothesis for converting original positive ENNReal mark moments into signed Radon uniqueness.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_test_support_separated
import Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_continuous_compact_test_integrable_on_finite_negative_band
open MeasureTheory Set Topology AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_compact_negative_integrable_of_locally_finite
    (μ : Measure ℝ)
    (hμ : ∀ ε : ℝ, 0 < ε → μ (Iic (-ε)) < ⊤)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    Integrable g μ := by sorry
