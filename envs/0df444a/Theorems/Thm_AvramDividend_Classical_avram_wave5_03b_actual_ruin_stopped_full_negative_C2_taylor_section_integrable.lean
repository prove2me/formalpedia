-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_section_integrable
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_section_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:03:43.62603+00:00
-- url     : https://prove2.me/theorems/400350d3-3ae1-4683-879b-3d99ca1a7a74
-- title:
--   Pointwise signed full-negative Lévy source integrability for actual stopped controlled Taylor kernel under general C²
-- statement:
--   For the literal original spectrally negative Lévy X and adapted D, the actual prepayment reserve and inclusively ruin-stopped nonlinear Taylor remainder is integrable against the full negative original X.nu for each fixed predictable time-sample, without global positivity or monotonicity on C2 w. Predictable measurability is inherited from the existing original source stopped L2 interface; the new full negative C2 source envelope yields an absolute dominating integrable Levy quadratic mark kernel. The zero auxiliary measure is used only to instantiate the independently proved measurability theorem, not as compensation or a Poisson replacement.
-- source:
--   Canonical Proved 5eef1de0 original source general C2 negative-mark bound, b62df142 original stopped predictability, and original X.nu_integrable; no Chat01 source compensator assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_compensated_taylor_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_section_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
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
