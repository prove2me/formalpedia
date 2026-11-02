-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_randomly_stopped_predictable_jump_sum
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_finite_horizon_randomly_stopped_predictable_jump_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:26:50.311189+00:00
-- url     : https://prove2.me/theorems/e0cd7438-3ad1-4286-8128-474b8b834180
-- title:
--   Actual source finite-horizon randomly stopped predictable marked integral equals literal same-path jump sum
-- statement:
--   For any actual original Lévy process X, original filtration 𝓕, a finite random stopping horizon τ, deterministic interval (s,t], Borel mark band B, and nonnegative 𝓕-predictable-by-Borel marked test H, its integral against the genuine intrinsic source jump measure is exactly the series over the actual path jumps satisfying u≤τ(ω), s<u≤t and mark∈B. The proof uses source jump-sum identity and measurability of the source sample-mark predictable lift. No copied Poisson law, compensator, BV, optional stopping theorem or other source law is postulated.
-- source:
--   Proved original intrinsic jump-sum e4542c93 and original predictable fixed-sample marked lift 95f32973.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_predictable_sample_mark_lift_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem AvramDividend.Classical.avram_wave5_01_actual_source_finite_horizon_randomly_stopped_predictable_jump_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (τ : Ω → ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ≥0∞)
    (hH : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H)
    (ω : Ω) :
    (∫⁻ p : ℝ≥0 × ℝ,
      (if s < p.1 ∧ p.1 ≤ t ∧ p.1 ≤ τ ω ∧ p.2 ∈ B
        then H ((p.1, ω), p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑' u : ℝ≥0,
      if 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then
        (if s < u ∧ u ≤ t ∧ u ≤ τ ω ∧
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ∈ B
          then H ((u, ω),
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u)
          else 0)
      else 0 := by sorry
