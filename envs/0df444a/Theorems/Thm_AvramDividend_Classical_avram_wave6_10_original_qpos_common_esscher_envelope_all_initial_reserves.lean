-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_qpos_common_esscher_envelope_all_initial_reserves
-- name    : AvramDividend.Classical.avram_wave6_10_original_qpos_common_esscher_envelope_all_initial_reserves
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:50:54.774652+00:00
-- url     : https://prove2.me/theorems/66533f34-2f65-4447-8fd7-9bf93fe660a7
-- title:
--   One positive Esscher tilt uniformly bounds original optimal dividend values for every starting reserve and cap
-- statement:
--   For every genuine original spectrally negative Lévy process and every positive discount rate q, there is one positive theta depending only on X and q, such that the exact source-probability expected original Stieltjes optimal dividend value at every initial reserve x and every cap C, including top, is bounded after scaling by ofReal theta by exp(theta*x). Crucially theta is chosen outside the forall-x quantifier, permitting global-in-x exponential growth estimates without Standing or any bounded-variation assumption. This reuses the Proved source small-tilt and original all-cap theta value bound and does not assert the unproved arbitrary C2 stochastic HJB core.
-- source:
--   Source exact Proved positive small tilt 6b7f5580-f12e-4a18-8862-48af9a18594f combined with source exact Proved all-reserve theta budget 24f9b5f0-00d4-4444-bb25-6d3a0cfcdb49. Strengthens fixed-x quantitative envelope b8070261 by exchanging one theta choice with the universal reserve quantifier, a genuine global-growth interface.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_theta_perpetual_capped_and_unrestricted_value_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_original_qpos_common_esscher_envelope_all_initial_reserves
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ x : ℝ,
      (∀ C : ℝ≥0∞,
        ENNReal.ofReal θ * valueFunctionLe X q C x ≤
          ENNReal.ofReal (Real.exp (θ * x))) ∧
      ENNReal.ofReal θ * valueFunction X q x ≤
        ENNReal.ofReal (Real.exp (θ * x)) := by sorry
