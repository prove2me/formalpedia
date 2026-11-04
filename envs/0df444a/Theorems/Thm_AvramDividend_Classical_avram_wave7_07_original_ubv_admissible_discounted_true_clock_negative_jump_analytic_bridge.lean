-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_discounted_true_clock_negative_jump_analytic_bridge
-- name    : AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_true_clock_negative_jump_analytic_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:21:28.428356+00:00
-- url     : https://prove2.me/theorems/e4424edd-ed0f-44ac-8e70-e8430573739b
-- title:
--   Original UBV discounted true-clock negative-jump and full HJB analytic bridge
-- statement:
--   Under exactly the canonical UBV admissibility, extended cap and source generator HJB conditions, construct the finite original physical predictable time clock. On this one clock, both the stopped negative Borel Lévy generator drift and the original nonlinear C² Taylor product are L¹ under true exponential discount; the full negative-mark compensation integral identity holds and the drift of the entire Lévy generator minus qw is integrable with nonpositive mean. This assembles proved source results 47,49,50,51 without inventing any stochastic jump-count identity; original intrinsic count compensation remains P2.
-- source:
--   W7-07 combined actual source analytic handoff to W7-08 stopped Ito residual verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_discounted_borel_negative_generator_finite_clock_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_discounted_borel_negative_taylor_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_discounted_borel_negative_generator_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_discounted_true_clock_HJB_drift_nonpositive

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_true_clock_negative_jump_analytic_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : ENNReal.ofReal v < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
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
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    let S : Set ((ℝ≥0 × Ω) × ℝ) := {r | r.2 ∈ Iio (0 : ℝ)}
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable (fun p : ℝ≥0 × Ω =>
        Real.exp (-(q * (p.1 : ℝ))) *
          (∫ z in Iio (0 : ℝ), G (p,z) ∂X.ν)) μ ∧
      Integrable (fun r : ((ℝ≥0 × Ω) × ℝ) =>
        (S.indicator (fun r => Real.exp (-(q * (r.1.1 : ℝ))) * HS r)) r) (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
          μ.prod (X.ν.restrict (Iio (0 : ℝ)))) ∧
      (∫ r : ((ℝ≥0 × Ω) × ℝ),
        (S.indicator (fun r => Real.exp (-(q * (r.1.1 : ℝ))) * HS r)) r
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
      (∫ p : ℝ≥0 × Ω,
        Real.exp (-(q * (p.1 : ℝ))) *
          (∫ z in Iio (0 : ℝ), G (p,z) ∂X.ν) ∂μ) ∧
      Integrable (fun p : ℝ≥0 × Ω =>
        Real.exp (-(q * (p.1 : ℝ))) * R p) μ ∧
      (∫ p : ℝ≥0 × Ω,
        Real.exp (-(q * (p.1 : ℝ))) * R p ∂μ) ≤ 0 := by sorry
