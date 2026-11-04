-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_laplace_gives_exact_intervals
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_laplace_gives_exact_intervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:53:30.350769+00:00
-- url     : https://prove2.me/theorems/134ce337-ef00-44aa-9615-4ecdd4379550
-- title:
--   Original BV finite-window exact physical drift from actual jump Laplace functional
-- statement:
--   Under original BV source and an explicitly assumed genuine negative-jump Laplace functional at θ≥1, prove on one original P-full event the uncompensated exact physical drift-minus-intrinsic-jumps formula simultaneously for all 0≤s≤t≤T. No Standing or first moments of total jumps/X_T. This isolates a heavy-tail-safe P2 input without any auxiliary process.
-- source:
--   Combines new original source exponential integrability, new conditional original jump-Laplace residual rigidity, and Proved monotone original BV source interval remainder. Uses exact hRzero and monotonicity to propagate the terminal identity to all earlier intervals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_physical_drift_exponential_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_jump_laplace_match_kills_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One authentic original-source jump Laplace functional forces the exact
BV physical-drift path identity on every interval within one horizon. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_laplace_gives_exact_intervals
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (θ : ℝ) (hθ : 1 ≤ θ)
    (hJInt : Integrable (fun ω : Ω =>
      Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal))) P)
    (hJLap : (∫ ω : Ω, Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
      Real.exp (-(T : ℝ) *
        (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν))) :
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
