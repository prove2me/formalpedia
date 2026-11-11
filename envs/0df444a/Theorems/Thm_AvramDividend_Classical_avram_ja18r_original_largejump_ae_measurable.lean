-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18r_original_largejump_ae_measurable
-- name    : AvramDividend.Classical.avram_ja18r_original_largejump_ae_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:46:47.531376+00:00
-- url     : https://prove2.me/theorems/948e2a97-5914-4195-bf77-dd34456a1825
-- title:
--   Original intrinsic large-negative jump sum is a.e. strongly measurable
-- statement:
--   For finite activity, the original marked-jump sum is a measurable function of the physical path and original probability space; no auxiliary source.
-- source:
--   AVRAM J-A18 original zero-cutoff Gaussian martingale integrability, 70393ec7 via 37d22393; all on same X and P.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18r_original_largejump_ae_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      AEStronglyMeasurable
        (fun ω => avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) P := by sorry
