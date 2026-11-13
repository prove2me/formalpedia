-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva67_original_natural_ruin_clipped_cash_mesh_error_mean_zero
-- name    : AvramDividend.Classical.avram_bva67_original_natural_ruin_clipped_cash_mesh_error_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:09:30.472052+00:00
-- url     : https://prove2.me/theorems/ba9bb0af-2726-4048-af10-970eb799c77f
-- title:
--   Original natural clipped-ruin strict discounted cash mesh error is integrable and mean-vanishing
-- statement:
--   For the actual infinite-activity-capable spectrally negative Levy process X, arbitrary admissible dividend D, positive integer horizon n and natural clipped ruin time rho=min(ruin(X,x,D),n), the exact source-specific positive physical mesh cash discount/contact error is integrable at each row and its expected value tends to zero. Source is the original stopped cash and no additional global generator integrability, independent replacement path or finite-activity assumption is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_natural_ruin_clock_full_stopping_package
import Theorems.Thm_AvramDividend_Classical_avram_bva66_original_strict_stopped_cash_mesh_error_expected_tendsto_zero
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva67_original_natural_ruin_clipped_cash_mesh_error_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    :
    let ρ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let F : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (n : ℝ)) * F + T
    (∀ m : ℕ, Integrable (E m) P) ∧
    Tendsto (fun m => ∫ ω, E m ω ∂P) atTop (nhds (0 : ℝ)) := by sorry
