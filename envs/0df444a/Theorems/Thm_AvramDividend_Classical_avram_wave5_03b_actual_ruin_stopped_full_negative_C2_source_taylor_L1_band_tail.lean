-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_band_tail
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_band_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:05:20.948388+00:00
-- url     : https://prove2.me/theorems/19668eea-2893-4c6e-92d4-6d142fd3ecce
-- title:
--   Full negative source nonlinear Taylor L1 band truncation limit for the actual stopped Lévy reserve under general C²
-- statement:
--   For the actual adapted controlled Lévy reserve and inclusive ruin stop, any decreasing sequence of measurable negative source mark sets Bn with empty intersection has vanishing absolute X.nu×μ source Taylor remainder intensity, uniformly under finite predictable μ. The test function needs only C2 interior, continuity on nonnegative reserves and zero on negative arguments, with no global positivity/monotonicity. This all-negative-mark domain extends the previously Proved near-zero-only arbitrary-C2 tail and is a source-coupled L1 limit for Chat03's nonlinear jump generator.
-- source:
--   Canonical Proved general C2 original-source uniform absolute Taylor bound 5eef1de0 plus canonical antitone energy tail iInf-zero theorem and X.nu_integrable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_integrable_mark_energy_tail_iInf_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_band_tail
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
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
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
    ∀ (B : ℕ → Set ℝ)
      (hBm : ∀ n, MeasurableSet (B n))
      (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
      (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅),
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) = 0 := by sorry
