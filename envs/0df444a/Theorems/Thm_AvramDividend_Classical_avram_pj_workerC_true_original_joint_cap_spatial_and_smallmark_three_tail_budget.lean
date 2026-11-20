-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_original_joint_cap_spatial_and_smallmark_three_tail_budget
-- name    : AvramDividend.Classical.avram_pj_workerC_true_original_joint_cap_spatial_and_smallmark_three_tail_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:28:49.88211+00:00
-- url     : https://prove2.me/theorems/2ed57b78-ac68-448a-a737-75211bec4cc3
-- title:
--   Original stopped finitecap joint spatial lower/upper reserve strips and same cutoff nonlinear Lévy small-mark L1/L2 and generator discrepancy quantitative localisation
-- statement:
--   For the actual original spectrally negative Lévy process X with unbounded variation and original admissible post-right dividends D, and genuine original finitecap Ccap, smooth interior compact C2 band, finite original physical time N, finite original sample product measure μsp and finite predictable measure μ, given any epsilon > 0 select spatial lower cutoff k, spatial cap cutoff j and one negative-mark exhaustion n so that the strictly positive lower reserve occupation is ≤epsilon, upper reserve occupation is ≤epsilon, and three original Lévy compensated Taylor L1, Taylor L2 and generator discrepancy negative-mark energies are each <epsilon. Both true physical-clock and predictable measures refer to the same original X,D. This is a quantitative joint localisation kit and does not claim the unresolved stochastic Itô decomposition.
-- source:
--   Proved 5e23a501 original finite-cap spatial upper/lower quantitative sources and f8c63678 original same smallmark negative cutoff for nonlinear Taylor L1/L2 and generator discrepancy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_finitecap_both_spatial_boundary_occupations_arbitrarily_small
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_three_tail_source_common_cutoff_epsilon
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_true_original_joint_cap_spatial_and_smallmark_three_tail_budget
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
    (hμ : μ Set.univ < ⊤)
    (T : ℝ≥0)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (hBV : ¬ X.BoundedVariation)
    (Ccap : ℝ≥0∞) (hCcap : 0 < Ccap)
    (hCfinite : Ccap ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ Ccap)
    (hDcap : IsAdmissibleLe X x Ccap D)
    (N : ℕ) (hN : 0 < N)
    (μsp : Measure (ℝ≥0 × Ω)) [IsFiniteMeasure μsp] :
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
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∀ ε : ℝ, 0 < ε →
      ∃ k j n : ℕ,
        μsp {p : ℝ≥0 × Ω |
          0 < riskProcess X x D p.1 p.2 ∧
          riskProcess X x D p.1 p.2 ≤
            (1 : ℝ) / ((k : ℝ) + 1)} ≤ ENNReal.ofReal ε ∧
        (∫ ω, ∫ t in Ioo (0 : ℝ) (N : ℝ),
          if Ccap.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
            riskProcess X x D (Real.toNNReal t) ω
          then (1 : ℝ) else 0 ∂volume ∂P) ≤ ε ∧
        (∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) <
            ENNReal.ofReal ε ∧
        (∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ) <
            ENNReal.ofReal ε ∧
        (∫⁻ p : ℝ≥0 × Ω,
          ‖(∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) -
            (∫ z in Iio (0 : ℝ) \ B n, JG (p,z) ∂X.ν)‖ₑ
          ∂(((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) <
            ENNReal.ofReal ε := by sorry
