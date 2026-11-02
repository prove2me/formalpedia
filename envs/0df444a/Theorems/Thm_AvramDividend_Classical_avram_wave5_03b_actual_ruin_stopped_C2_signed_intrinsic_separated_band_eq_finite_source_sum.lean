-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_C2_signed_intrinsic_separated_band_eq_finite_source_sum
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_C2_signed_intrinsic_separated_band_eq_finite_source_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:24:42.608056+00:00
-- url     : https://prove2.me/theorems/55f66f79-876a-43c3-add4-1375e0536b3b
-- title:
--   Actual ruin-stopped nonlinear C² Taylor signed intrinsic source band integral is integrable and equals the genuine finite source jump sum
-- statement:
--   For the actual original spectrally negative Lévy source X and adapted dividends D, on every finite clock interval and every negative source-mark band measurably separated from zero, the signed ruin-stopped prepayment C² Taylor correction is automatically integrable against the literal intrinsic original marked source jump measure, and its signed Bochner integral equals the finite sum over exactly the genuine same-path source jumps. This discharges rather than assumes pathwise fibre integrability.
-- source:
--   Canonical Proved original-source stopped nonlinear absolute marked finite-band equality 8feca54c; Proved original signed marked finite-band integral summation b881e8e7; original stopped predictable C² Taylor kernel 0e0663b1; pinned ENNReal.sum_lt_top and Real.enorm_eq_ofReal_abs. No independent Poisson copy or assumed finite jump set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_separated_band_absolute_taylor_intrinsic_eq_finite_source_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_intrinsic_signed_finite_band_integral_eq_actual_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_C2_signed_intrinsic_separated_band_eq_finite_source_sum
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
    (huv : u + δ < v) (hv : v < C)
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let J : ℝ≥0 → Ω → ℝ := fun r η =>
      X.X r η - Function.leftLim (fun z : ℝ≥0 => X.X z η) r
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun η =>
      ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ J r η ≠ 0}).map
        (fun r : ℝ≥0 => (r, J r η)))
    let G : ℝ≥0 × ℝ → ℝ := fun p =>
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then HS ((p.1,ω),p.2) else 0
    ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable G (NX ω) ∧
      (∫ p : ℝ≥0 × ℝ, G p ∂NX ω) =
        ∑ r ∈ T, HS ((r,ω),J r ω) := by sorry
