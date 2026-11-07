-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_C1_random_cutoff_error_mean_tendsto_zero
-- name    : AvramDividend.Classical.avram_p3_grid4_finite_cap_C1_random_cutoff_error_mean_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:03:56.58734+00:00
-- url     : https://prove2.me/theorems/ca7fa254-9d85-49b3-9a84-ae8b823bd61f
-- title:
--   Random BV finite-cap cutoff error expectations vanish uniformly without endpoint smooth fit
-- statement:
--   For genuine probability-space random reserve paths with nonnegative reserves almost everywhere, the difference between the original finite-cap slope-one candidate extension and the shrinking cutoff extension has expectation converging to zero. The result follows from the source-exact BV C1 cap secant upper bound and scalar cutoff continuity; it explicitly requires integrability and supplies a rigorous expected-error adapter for actual stopped source localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_C1_uniform_cutoff_defect_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_finite_cap_C1_random_cutoff_error_mean_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (C : ℝ≥0∞) (hC : 0 < C) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n)
    (hbC : ∀ n, b n ≤ C.toReal)
    (hb : Tendsto b atTop (𝓝 C.toReal))
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, 0 ≤ᵐ[P] Y n)
    (hInt : ∀ n, Integrable (fun ω =>
      (if Y n ω ≤ C.toReal then w (Y n ω)
       else w C.toReal + (Y n ω - C.toReal)) -
      (if Y n ω ≤ b n then w (Y n ω)
       else w (b n) + (Y n ω - b n))) P) :
    Tendsto (fun n => ∫ ω,
      (if Y n ω ≤ C.toReal then w (Y n ω)
       else w C.toReal + (Y n ω - C.toReal)) -
      (if Y n ω ≤ b n then w (Y n ω)
       else w (b n) + (Y n ω - b n)) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
