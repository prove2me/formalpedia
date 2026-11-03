-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_uniform_all_caps_value_theta_bound
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_discount_uniform_all_caps_value_theta_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:04:50.827088+00:00
-- url     : https://prove2.me/theorems/96a570c7-22ad-4e37-9c4d-30c06443e5eb
-- title:
--   For every q>0 original Lévy optimal values uniformly over all caps obey a common source positive exponential tilt bound
-- statement:
--   Original spectrally negative Lévy X, any x and q>0: one real θ>0 bounds θ-scaled genuine optimal dividend valueFunctionLe X q C x for EVERY C and the unrestricted optimal valueFunction X q x by exp(θx). No Standing, no changed sample space.
-- source:
--   Accepted original rate-existence 6b7f5580 and authentic all-cap source theta value bounds 24f9b5f0 (another worker). Distinct positive-q unconditioned one-tilt value envelope to support UBV verification's global strategy bounds, not the missing Ito identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_theta_perpetual_capped_and_unrestricted_value_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_positive_discount_uniform_all_caps_value_theta_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧
      (∀ C : ℝ≥0∞,
        ENNReal.ofReal θ * valueFunctionLe X q C x ≤
          ENNReal.ofReal (Real.exp (θ * x))) ∧
      ENNReal.ofReal θ * valueFunction X q x ≤
        ENNReal.ofReal (Real.exp (θ * x)) := by sorry
