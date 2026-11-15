-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a31_original_gaussian_source_ae_representative_measurable_20261114
-- name    : AvramDividend.Classical.avram_a31_original_gaussian_source_ae_representative_measurable_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:44:38.073978+00:00
-- url     : https://prove2.me/theorems/d873f612-5974-44cf-9943-80952958e502
-- title:
--   Every original intrinsic Gaussian cutoff limit representative is a.e. measurable at each time
-- statement:
--   The original finite-activity Gaussian intrinsic residual limit admits a globally raw-adapted representative. Any other process agreeing with the physical limit simultaneously on a conull set is measurable at each fixed time modulo the original probability measure.
-- source:
--   Proved A24 raw adapted Gaussian representative and Mathlib AEMeasurable.congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Any pointwise a.e. representative of the original intrinsic Gaussian limit is a.e. measurable at each physical time. -/

theorem AvramDividend.Classical.avram_a31_original_gaussian_source_ae_representative_measurable_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ t : ℝ≥0, AEMeasurable (G t) P := by sorry
