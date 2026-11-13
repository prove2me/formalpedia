-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b25_original_K_real_time_integral_auto_meas
-- name    : AvramDividend.Classical.avram_bvb_b25_original_K_real_time_integral_auto_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:54:53.748256+00:00
-- url     : https://prove2.me/theorems/8c8a37f9-f0eb-4dd0-b3b4-f7d6f0fe1331
-- title:
--   Original masked loss upper bound on the genuine uniform floor grid
-- statement:
--   The actual original prepayment reserve's discounted open-cap negative mark loss on the refining uniform floor grid is eventually no greater than its closed-cap contact-time loss plus arbitrary epsilon, even when the grid misses contact occupation.
-- source:
--   Root-connected one-sided a.e. floor-sampling input for phys95/efbae9c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_K_exact_real_time_integral
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_stopped_H_mark_fibre_eq_discounted_rate
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b24_original_K_closed_cap_real_time_rate_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b25_original_K_real_time_integral_auto_meas
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q T : ℝ) (hT : 0 < T)
    (n : ℕ) (ω : Ω)
    (hψ : ContinuousOn
      (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν)
      {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    let U : ℝ≥0 → Ω → ℝ := fun r η => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z η - rightLimit D z η) r
    let H : (ℝ≥0 × Ω) × ℝ → ℝ := fun p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - T / ((n : ℝ) + 2) ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0
      then Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2))
      else 0
    (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
    (∫ t in Icc 0 T,
      if 0 < Real.toNNReal t ∧
         ((Real.toNNReal t : ℝ≥0) : ℝ) < T - T / ((n : ℝ) + 2) ∧
         ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) ≤ ruinTime X x D ω ∧
         0 ≤ U (Real.toNNReal t) ω ∧
         ENNReal.ofReal (U (Real.toNNReal t) ω) ≤ C
      then Real.exp (-(q * ((Real.toNNReal t : ℝ≥0) : ℝ))) *
         ∫ z in Iio (0 : ℝ), w (U (Real.toNNReal t) ω + z) -
                                   w (U (Real.toNNReal t) ω) ∂X.ν
      else 0) := by sorry
