-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_stopped_L1_L2_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_stopped_L1_L2_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:58:17.697025+00:00
-- url     : https://prove2.me/theorems/3606a365-76a2-4c7c-8901-41c77b39af31
-- title:
--   Actual original finite-horizon stopped nonlinear jump drift and quadratic energies converge to zero on shrinking negative marks
-- statement:
--   On the original spectrally negative Lévy source and adapted dividend policy, construct a finite predictable measure agreeing with the genuine horizon-trimmed Lebesgue time × original probability measure. For the actual prepayment Taylor remainder stopped inclusively at controlled ruin, prove ordinary Tendsto atTop to zero for both the absolute L1 generator-drift mark mass and quadratic L2 jump energy on every shrinking measurable negative mark family contained in the C2 near-jump radius. This strengthens the prior iInf-zero analytical statement into the standard tail convergence required to feed a genuine source isometry once Chat 01/02 prove it, without assuming one now.
-- source:
--   Canonical Proved actual finite-horizon time-P nonlinear joint tails 46258bcf-62db-4de2-84ef-431f86efd5f6; pinned Mathlib tendsto_atTop_iInf and lintegral_mono_set; antitone shrinking negative mark sets. The stopped source X, same adapted D, actual X.nu and time-P predictable μ remain unchanged. This is analytical intensity convergence, not an unproved Poisson compensated martingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_stopped_L1_L2_tendsto_zero
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
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ f : (ℝ≥0 × Ω) → ℝ≥0∞,
        Measurable[𝓕.rightCont.predictable] f →
        (∫⁻ p, f p ∂μ) =
          (∫⁻ p, f p ∂((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P))) ∧
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
      ∃ r : ℝ, 0 < r ∧
        ∀ (B : ℕ → Set ℝ)
          (hBm : ∀ n, MeasurableSet (B n))
          (hBnear : ∀ n, B n ⊆ Ioo (-r) 0)
          (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅),
        Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ)
          atTop (𝓝 0) ∧
        Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ)
          atTop (𝓝 0) := by sorry
