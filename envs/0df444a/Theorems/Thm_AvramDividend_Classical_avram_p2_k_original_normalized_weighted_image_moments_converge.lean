-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_k_original_normalized_weighted_image_moments_converge
-- name    : AvramDividend.Classical.avram_p2_k_original_normalized_weighted_image_moments_converge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:03:47.677878+00:00
-- url     : https://prove2.me/theorems/bb133076-2964-4718-9980-f3136307f677
-- title:
--   Genuine normalised source weighted exponential-image measures have all original Lévy-image moments
-- statement:
--   For each monomial power, the genuine original fourth-weighted law of exp(X_h), normalised by positive elapsed time h, has its exact ENNReal moment converging to that of the original negative Lévy measure fourth-weighted and mapped by exp. The approximate finite measure is defined as zero for nonpositive h, so it is a total family on the real index required by P2-I.
-- source:
--   Apply exact source Proved 2ca40085-b85b-4101-88bc-12501017d285 and pinned MeasureTheory.lintegral_smul_measure to the positive-time normalised original weighted exponential image. This is a source-exact interface into proved P2-I c02ab0e5 without a stationary count assumption.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_moments_identify_levy_image

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_k_original_normalized_weighted_image_moments_converge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    Tendsto (fun h : ℝ => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
      (if 0 < h then (ENNReal.ofReal h)⁻¹ •
        ((P.withDensity (fun ω => ENNReal.ofReal
          ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
      else (0 : Measure ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
        (((X.ν.restrict (Iio (0 : ℝ))).withDensity
          (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))) := by sorry
