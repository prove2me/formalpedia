-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_source_taylor_L1_integrable
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_source_taylor_L1_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:47:03.754205+00:00
-- url     : https://prove2.me/theorems/3e453765-206f-4a2d-9464-5509f05856ac
-- title:
--   Full negative Lévy source-mark L1 integrability of the actual ruin-stopped nonlinear Taylor remainder
-- statement:
--   For the literal SpectrallyNegativeLevy source X and an adapted original dividend control D, the actual left-limit prepayment reserve and inclusive ruin stopping, the full negative-mark nonlinear Taylor kernel is absolutely integrable against the original Lévy intensity X.ν at each time and sample. The source 1_{z>-1} truncation is retained. The global monotonicity/nonnegativity of the C² test function is explicitly assumed to control large negative marks, and no source compensator or Poisson independence is asserted.
-- source:
--   Canonical proved original source Taylor identification e336f7e2, full stopped predictable L2-measurability b62df142, uniform monotone generator bound c9a18a64, and X.nu_integrable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_compensated_taylor_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_source_taylor_L1_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hnonneg : ∀ z : ℝ, 0 ≤ w z) (hmono : Monotone w)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C) :
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
    ∀ p : ℝ≥0 × Ω,
      Integrable (fun z : ℝ => HS (p,z)) (X.ν.restrict (Iio (0 : ℝ))) := by sorry
