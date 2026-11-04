-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_generator_continuous_and_jump_stieltjes_pair
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_generator_continuous_and_jump_stieltjes_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:37:55.299766+00:00
-- url     : https://prove2.me/theorems/e9947de3-fbe4-4416-909c-1c2c9e252090
-- title:
--   Original BV generator aligns with continuous atomless residual and actual raw-jump Stieltjes measures
-- statement:
--   For the original spectrally negative BV Levy process and its true generator, the generator uses precisely the same source physical drift d as two simultaneous almost-sure Stieltjes measures: the atomless continuous drift-removal remainder with exact interval masses, and the genuine source negative left-jump measure with exact interval and positive-time singleton masses. No auxiliary process, extra decomposition hypothesis or postulated Lévy rate is required.
-- source:
--   Combines Proved source generator physical drift representation c8ba98f0 with the accepted atomless original BV residual Stieltjes measure 14795a0f; adds the true raw negative-jump Stieltjes function, its original strict-past left limit 73032d17, and original endpoint splitting 2f1436db via the pinned measure_Ioc and measure_singleton lemmas.

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_generator_continuous_and_jump_stieltjes_pair
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (X.generator w x = X.drift * deriv w x +
      ∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) ∧
    (∀ᵐ ω ∂P, ∃ μr μj : Measure ℝ≥0,
      (∀ a b : ℝ≥0, a ≤ b → μr (Ioc a b) = ENNReal.ofReal (
        ((((b : ℝ) * X.drift - X.X b ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
        (((a : ℝ) * X.drift - X.X a ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))))) ∧
      (∀ a : ℝ≥0, μr {a} = 0) ∧
      (∀ a b : ℝ≥0, a ≤ b → μj (Ioc a b) = ENNReal.ofReal (
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) ∧
      (∀ t : ℝ≥0, 0 < t → μj {t} = ENNReal.ofReal
        (Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω))) := by sorry
