-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_stopped_fulltime_boundary_weight_zero_of_ae_positive
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ruin_stopped_fulltime_boundary_weight_zero_of_ae_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:32:33.987271+00:00
-- url     : https://prove2.me/theorems/227f802b-0070-4b5d-82a9-d536dcbea9cc
-- title:
--   Original stopped UBV physical-time boundary contact weight is zero including the initial time when time measure does not charge zero
-- statement:
--   The original stopped UBV contact occupation weight vanishes for all strict pre-ruin physical times, now without the t>0 restriction, provided the deterministic sigma-finite time measure has no mass at t=0. This resolves the only extra endpoint term left by the already Proved positive-time source contact theorem. The measure is physical time, not dividend Stieltjes, so this does not discard initial dividend atoms.
-- source:
--   Already Proved source original P4-E joint boundary occupation e9e42507 and Mathlib lintegral_congr_ae, zero-null physical time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_stopped_positive_time_joint_boundary_weight_zero
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Strict pre-ruin zero/cap occupation vanishes also at t=0 under an atomless initial physical clock. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_ruin_stopped_fulltime_boundary_weight_zero_of_ae_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D s ω ≤ c)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ]
    (hμZero : ∀ᵐ t : ℝ≥0 ∂μ, t ≠ 0)
    (weight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0, if (t : ℝ≥0∞) < τ ω ∧
        (riskProcess X x D t ω = 0 ∨ riskProcess X x D t ω = c)
        then weight t ω else 0 ∂μ) = 0 := by sorry
