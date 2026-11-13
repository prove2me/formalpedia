-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva71_original_arbitrary_real_horizon_clipped_ruin_cash_error_certificate
-- name    : AvramDividend.Classical.avram_bva71_original_arbitrary_real_horizon_clipped_ruin_cash_error_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:38:04.23221+00:00
-- url     : https://prove2.me/theorems/1f247b2d-89fc-4765-b6c0-b6c160485504
-- title:
--   Any original real ruin-clipped horizon admits a physical mesh with integrable vanishing contact and cash correction
-- statement:
--   For every finite real nonnegative horizon T without a prespecified integer upper bound, the authentic spectrally negative Levy process and any admissible dividend strategy admit a positive integer physical mesh clock bound n≥T. The strict stopped discounted cash/ruin-contact physical mesh correction with width n/(m+2) is integrable in every row and its expectation converges to zero. This removes the extra horizon upper bound from Proved BVA70 by an Archimedean choice n=ceil(T)+1 and does not introduce a finite-activity replacement or global generator-L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva70_original_real_horizon_strict_clipped_ruin_cash_mesh_error_L1_vanish
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem AvramDividend.Classical.avram_bva71_original_arbitrary_real_horizon_clipped_ruin_cash_error_certificate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (T : ℝ≥0) :
    ∃ n : ℕ, 0 < n ∧ T ≤ (n : ℝ≥0) ∧
    (let ρ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
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
    Tendsto (fun m => ∫ ω, E m ω ∂P) atTop (nhds (0 : ℝ))) := by sorry
