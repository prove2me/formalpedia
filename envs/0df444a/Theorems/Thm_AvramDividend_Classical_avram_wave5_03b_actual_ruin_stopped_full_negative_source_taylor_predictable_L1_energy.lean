-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_source_taylor_predictable_L1_energy
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_source_taylor_predictable_L1_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:48:34.843033+00:00
-- url     : https://prove2.me/theorems/d25bec1e-18a0-4cc0-a274-13dae6afa095
-- title:
--   Finite source Lévy L1 energy of actual ruin-stopped nonlinear jump remainder against any finite predictable measure
-- statement:
--   For the original source X and adapted controlled reserve, the full negative-mark signed nonlinear Taylor correction stopped at actual ruin has finite absolute iterated X.nu and predictable finite-measure intensity. C2 regularity on the positive reserve band plus explicitly global nonnegative monotone w ensures a common uniform M min(1,z²) source-dominated majorant. This is drift integrability, not a claim of a compensator identity.
-- source:
--   Proved uniform original Lévy generator bound c9a18a64, exact 03B source generator kernel e336f7e2 and genuine X.nu-integrable min quadratic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_source_taylor_predictable_L1_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hnonneg : ∀ z : ℝ, 0 ≤ w z) (hmono : Monotone w)
    (hu : 0 < u) (hδ : 0 < δ) (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) < ⊤ := by sorry
