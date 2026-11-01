-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_weighted_kernel_joint_measurable
-- name    : AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_weighted_kernel_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:46:42.826387+00:00
-- url     : https://prove2.me/theorems/ccb96bbc-54d8-4536-b949-1592034dc36d
-- title:
--   Joint Borel measurability of the genuinely compensated integrated scale kernel
-- statement:
--   For the genuine unbounded-variation spectrally negative Lévy source scale W, its global interval primitive U(x)=∫₀ˣW is monotone and Borel, and its derivative is precisely W on the whole real line. Consequently the original compensated generatorIntegrand U(x,y), weighted by exp(-θx) and its absolute value, is jointly Borel measurable on real reserve/jump pairs. This is a concrete missing product-measurability input for the quadratic small-jump and finite-mass large-jump Fubini step; it assumes neither generator harmonicity nor any stopped-scale conclusion.
-- source:
--   Avram Palmowski Pistorius 2007, Section 3 and Lemma 4; existing Proved primitive derivative identity a9a01dd4, scale measurability 344f3813 and original generator joint measurability 917f8349.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_weighted_kernel_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) :
    Measurable
      (fun p : ℝ × ℝ => Real.exp (-θ * p.1) *
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) p.1 p.2|) := by sorry
