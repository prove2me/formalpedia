-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_negative_C2_taylor_finite_source_band_sum_exhaustion
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_negative_C2_taylor_finite_source_band_sum_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:08:21.345527+00:00
-- url     : https://prove2.me/theorems/623c7376-633b-4428-aa8e-d1c68df7acc8
-- title:
--   Actual stopped original negative C² Taylor source jump correction as supremum of increasing finite true-source jump sums
-- statement:
--   For the original Lévy X and adapted dividends D, any increasing measurable negative bands separated from zero and covering all negative marks admit a monotone family of finite genuine source-jump times; the supremum of the inclusive ruin-stopped nonlinear C² Taylor absolute correction over those source times equals its full negative-mark intrinsic marked-measure integral (which may be infinite).
-- source:
--   Composition of canonical Proved 03B separated finite-source-band stopped nonlinear C² Taylor intrinsic integral equality 8feca54c with Proved actual full negative band exhaustion 2a743fed; the monotonic Finset property is established from exact source-jump membership and monotone bands. No generic Poisson copy, compensator, or unattested finiteness assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_separated_band_absolute_taylor_intrinsic_eq_finite_source_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_absolute_taylor_source_jump_band_exhaustion

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_negative_C2_taylor_finite_source_band_sum_exhaustion
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
    (B : ℕ → Set ℝ) (hBmeas : ∀ n, MeasurableSet (B n))
    (hBmono : Monotone B)
    (hBcover : ∀ z : ℝ, z < 0 ↔ ∃ n : ℕ, z ∈ B n)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hBsep : ∀ n z, z ∈ B n → ε n ≤ dist z 0)
    (s t : ℝ≥0) (ω : Ω) :
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
    ∃ T : ℕ → Finset ℝ≥0,
      (∀ (n : ℕ) (r : ℝ≥0), r ∈ T n ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B n) ∧
      (∀ n : ℕ, T n ⊆ T (n + 1)) ∧
      (⨆ n : ℕ, ∑ r ∈ T n, ENNReal.ofReal (|HS ((r,ω),J r ω)|)) =
      (∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω) := by sorry
