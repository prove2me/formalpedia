-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b52_original_gaussian_and_marked_jump_predictable_cell_centered
-- name    : AvramDividend.Classical.avram_b52_original_gaussian_and_marked_jump_predictable_cell_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:06:21.130908+00:00
-- url     : https://prove2.me/theorems/494df26f-cfc8-4189-ba87-226249445680
-- title:
--   Same original Levy Gaussian and actual nonlinear Borel jump-mark predictable stochastic cells are jointly centred
-- statement:
--   Construct the actual continuous intrinsic Gaussian martingale on the same finite-activity spectrally negative Levy path and filtration. Any integrable predictable weighted Gaussian increment plus a square-integrable predictable coefficient times a genuine negative Borel marked compensated jump count on a physical cell is jointly integrable and has exactly zero expectation. No independent Gaussian proxy, no global mark-square moment, and no unbounded post-ruin clock are introduced.
-- source:
--   Proved B31 original Gaussian residual existence; JB20 predictable Gaussian mean-zero cell; P4-F3 actual original marked Borel jump compensated predictable mean-zero cell.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_past_weight_increment_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b52_original_gaussian_and_marked_jump_predictable_cell_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (R t ω))) ∧
      ∀ (T : ℝ≥0) (cut : ℕ)
        (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
        (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
        (hB : MeasurableSet B)
        (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
        (hCut : B ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
        (HG HJ : Ω → ℝ)
        (hHG : Measurable[𝓕.rightCont s] HG)
        (hHJI : StronglyMeasurable[𝓕 s] HJ)
        (hHJ2 : MemLp HJ 2 P)
        (hGI : Integrable (fun ω =>
          HG ω * (R t ω - R s ω)) P),
        let N : Ω → ℝ≥0∞ := fun ω =>
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc s t ×ˢ B)
        let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
        Integrable (fun ω =>
          HG ω * (R t ω - R s ω) + HJ ω * ((N ω).toReal - r)) P ∧
        (∫ ω, HG ω * (R t ω - R s ω) +
          HJ ω * ((N ω).toReal - r) ∂P) = 0 := by sorry
