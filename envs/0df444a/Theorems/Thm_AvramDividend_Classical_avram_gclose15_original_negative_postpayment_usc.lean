-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose15_original_negative_postpayment_usc
-- name    : AvramDividend.Classical.avram_gclose15_original_negative_postpayment_usc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:41:51.311279+00:00
-- url     : https://prove2.me/theorems/5b13a627-9685-4f15-8ceb-132cc84d9b0f
-- title:
--   Negative original postpayment reserve is upper semicontinuous on compact prefixes
-- statement:
--   For every sample path of the original spectrally negative Levy surplus process controlled by an admissible dividend strategy, the negative postpayment reserve is upper semicontinuous on each compact nonnegative time prefix. The result follows from the original cadlag reserve and absence of positive reserve jumps, without any Gaussian coupling, stopped Ito assumption, or filtration change. This is a necessary deterministic path regularity premise for a uniform positive reserve floor in top-cap Gaussian localisation.
-- source:
--   The exact original postPaymentReserve_cadlag_adapted a2763475 gives right continuity, and avram_wave3_04_postPaymentReserve_no_positive_jumps 51ff3291 gives left limits with downward-only reserve jumps. Negate the path and apply the Proved cadlag_no_downward_jumps_upperSemicontinuousOn_Icc 95786bc2; then Proved usc_compact_prefix_sup_strictly_below_level b2aaf6e5 provides the deterministic uniform floor once positivity is established at all pre-ruin times.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_no_positive_jumps
import Theorems.Thm_AvramDividend_Classical_cadlag_no_downward_jumps_upperSemicontinuousOn_Icc
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose15_original_negative_postpayment_usc
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    UpperSemicontinuousOn
      (fun t : ℝ≥0 => -(x + X.X t ω - rightLimit D t ω))
      (Icc 0 T) := by sorry
