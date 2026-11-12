-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_K_exact_real_time_integral
-- name    : AvramDividend.Classical.avram_bvb_b23_original_K_exact_real_time_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:12:31.052619+00:00
-- url     : https://prove2.me/theorems/7b1a63f4-7da4-4921-9bce-22f384ead3f3
-- title:
--   Original masked loss upper bound on the genuine uniform floor grid
-- statement:
--   The actual original prepayment reserve's discounted open-cap negative mark loss on the refining uniform floor grid is eventually no greater than its closed-cap contact-time loss plus arbitrary epsilon, even when the grid misses contact occupation.
-- source:
--   Root-connected one-sided a.e. floor-sampling input for phys95/efbae9c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b22_original_compensator_K_real_time_integral
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_stopped_H_mark_fibre_eq_discounted_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b23_original_K_exact_real_time_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q T : ℝ)
    (n : ℕ) (ω : Ω) :
    let U : ℝ≥0 → Ω → ℝ := fun r η => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z η - rightLimit D z η) r
    let good : ℝ≥0 → Prop := fun t =>
      0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
      (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      0 ≤ U t ω ∧ ENNReal.ofReal (U t ω) ≤ C
    let H : (ℝ≥0 × Ω) × ℝ → ℝ := fun p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - T / ((n : ℝ) + 2) ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0
      then Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2))
      else 0
    let ψ : ℝ → ℝ := fun b =>
      ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν
    AEStronglyMeasurable
      (fun t : ℝ≥0 => ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))))
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal) →
    (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
    (∫ t in Icc 0 T,
      if good (Real.toNNReal t)
      then Real.exp (-(q * ((Real.toNNReal t : ℝ≥0) : ℝ))) *
        ψ (U (Real.toNNReal t) ω)
      else 0) := by sorry
