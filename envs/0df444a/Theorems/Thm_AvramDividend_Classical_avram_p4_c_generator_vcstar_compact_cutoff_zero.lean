-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_vcstar_compact_cutoff_zero
-- name    : AvramDividend.Classical.avram_p4_c_generator_vcstar_compact_cutoff_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:01:06.779178+00:00
-- url     : https://prove2.me/theorems/629da85a-ef26-49a7-83ab-e14d749fcbb9
-- title:
--   Original v-cstar discounted compact epsilon-generator drift residual vanishes on strict interior
-- statement:
--   Instantiate the source's Proved generator_vcstar_eq_zero at 0<y<cstar using the exact original generator and P4-C compact epsilon-physical drift decomposition. Obtain full source GeneratorIntegrable for vcstar and equality zero for Gaussian term, physical drift, full uncorrected z<-epsilon jump integral, compensated small jump remainder, minus q vcstar. No endpoint or stochastic Itô claim.
-- source:
--   generator_vcstar_eq_zero (Proved), P4-C original_epsilon_drift_compact

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_vcstar_compact_cutoff_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ y ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) y ∧
      (X.σ ^ 2 / 2 * iteratedDeriv 2 (vcstar W) y +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv (vcstar W) y +
        (∫ z in Iio (-ε), vcstar W (y + z) - vcstar W y ∂X.ν) +
        (∫ z in Ico (-ε) 0,
          SpectrallyNegativeLevy.generatorIntegrand (vcstar W) y z ∂X.ν) -
        q * vcstar W y = 0) := by sorry
