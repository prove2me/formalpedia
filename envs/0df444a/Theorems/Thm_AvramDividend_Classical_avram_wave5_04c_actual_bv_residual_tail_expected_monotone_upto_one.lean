-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_expected_monotone_upto_one
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_tail_expected_monotone_upto_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:45:14.501331+00:00
-- url     : https://prove2.me/theorems/763e91d3-008a-419c-a7a9-8a0664b1be90
-- title:
--   Actual bounded-variation Lévy residual expected first-moment tails increase in time
-- statement:
--   Under genuine Standing and BoundedVariation hypotheses, for 0≤t≤1 and any real cutoff M, the expectation of R_t 1_{R_t>M} is bounded above by that of R_1 1_{R_1>M}, with R_s=s X.drift-X_s the original Lévy physical drift deficit. Both real expectations are integrable by the proved original-source truncated-tail theorem; on the common source BV monotonicity event, 0≤R_t≤R_1, and a direct two-case analysis proves that r↦r1_{r>M} is nondecreasing on the nonnegative range. Integrate the pointwise inequality by Mathlib integral_mono_ae. No replacement process or source compensation assumptions are involved.
-- source:
--   Source-complete private Prove2Me remote compiler-passed candidate candidates/work_on/AvramDividend_04c_actual_residual_tail_monotone_integral_probe.lean; not yet proof submitted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_tail_expected_monotone_upto_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (t : ℝ≥0) (ht : t ≤ 1) (M : ℝ) :
    (∫ ω, if M < (t : ℝ) * X.drift - X.X t ω
      then (t : ℝ) * X.drift - X.X t ω else 0 ∂P) ≤
    (∫ ω, if M < (1 : ℝ) * X.drift - X.X 1 ω
      then (1 : ℝ) * X.drift - X.X 1 ω else 0 ∂P) := by sorry
