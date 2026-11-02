-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_bounded_time_weight_signed_intrinsic_band
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_bounded_time_weight_signed_intrinsic_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:41:29.094684+00:00
-- url     : https://prove2.me/theorems/29445631-5172-417a-a0fa-5d47b54cb939
-- title:
--   Bounded time weighted stopped signed intrinsic original source Levy jump integral equals exact marked finite band sum
-- statement:
--   For actual original SpectrallyNegativeLevy X with any adapted dividend D, a prepayment-reserve stopped C² Taylor remainder integrated against the intrinsic marked source measure may be multiplied by any measurable globally bounded deterministic time weight. Construct its precise original source jump Finset, prove weighted fibre integrability automatically, and identify the signed Bochner integral with the time-weighted original jump sum. This includes nonnegative-rate exponential discounting once elementary weight bounds are supplied.
-- source:
--   Depends on the canonical Proved original signed stopped C² finite source band 55f66f79-876a-43c3-add4-1375e0536b3b, genuine source signed finite-band summation b881e8e7-8c17-4354-822b-33855df6c8f1 and original stopped predictable Taylor measurability 0e0663b1. No Poisson independence or martingale construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_C2_signed_intrinsic_separated_band_eq_finite_source_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_intrinsic_signed_finite_band_integral_eq_actual_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_bounded_time_weight_signed_intrinsic_band
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
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0)
    (a : ℝ≥0 → ℝ) (ha : Measurable a)
    (M : ℝ) (ha_bound : ∀ r : ℝ≥0, |a r| ≤ M) :
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
    let GW : ℝ≥0 × ℝ → ℝ := fun p =>
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then
        a p.1 * HS ((p.1,ω),p.2) else 0
    ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable GW (NX ω) ∧
      (∫ p : ℝ≥0 × ℝ, GW p ∂NX ω) =
        ∑ r ∈ T, a r * HS ((r,ω),J r ω) := by sorry
