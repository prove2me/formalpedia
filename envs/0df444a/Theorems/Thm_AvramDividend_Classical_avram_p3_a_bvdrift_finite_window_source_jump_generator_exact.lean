-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_finite_window_source_jump_generator_exact
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_finite_window_source_jump_generator_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:20:16.049433+00:00
-- url     : https://prove2.me/theorems/3aa7d624-87fe-4635-af07-d2986cc86627
-- title:
--   Exact original BV finite-window jump increments and physical generator under one source moment normalisation
-- statement:
--   For the same Standing BV spectrally negative Lévy source, if the explicit original intrinsic residual at a single finite horizon T is integrable and mean zero, then the uncompensated original-source jump integral provides every increment X_t-X_s for 0≤s≤t≤T, simultaneously almost surely, and the identical original Lévy physical drift is the coefficient of the source generator at every generator-integrable test value. This is conditional on a genuine original-source mean identity; it does not introduce a different process or imply the missing compensator.
-- source:
--   P3-A integration helper combining newly accepted f17e2a9d and b15fec19. It identifies the single horizon residual as zero, propagates to every earlier time using the common monotone original-source residual, and substitutes in the exact interval source equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_source_interval_generator_alignment
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_single_mean_zero_horizon_gives_all_prior_jump_decomposition

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One first-moment normalisation supplies source physical-generator alignment
and exact intrinsic-jump increment decomposition over all subintervals of T. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_finite_window_source_jump_generator_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (hIntegrable : Integrable (fun ω : Ω =>
      ((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) P)
    (hMeanZero : (∫ ω : Ω,
      (((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) ∂P) = 0)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (X.generator w x = X.drift * deriv w x +
      ∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) ∧
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      X.X t ω - X.X s ω =
        ((t : ℝ) - (s : ℝ)) * X.drift -
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by sorry
