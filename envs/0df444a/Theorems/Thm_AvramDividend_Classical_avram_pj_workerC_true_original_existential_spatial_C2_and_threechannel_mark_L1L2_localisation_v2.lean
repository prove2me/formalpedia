-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_original_existential_spatial_C2_and_threechannel_mark_L1L2_localisation_v2
-- name    : AvramDividend.Classical.avram_pj_workerC_true_original_existential_spatial_C2_and_threechannel_mark_L1L2_localisation_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:51:14.656465+00:00
-- url     : https://prove2.me/theorems/368ad695-05b5-405f-a36a-072f0fb8eb8b
-- title:
--   Original finitecap physical spatial C2 band and negative Lévy mark cofinal quantitative localisation jointly exists for every epsilon
-- statement:
--   For the genuine original unbounded-variation spectrally negative Lévy process, any original admissible right dividend strategy, finite reserve cap Ccap, candidate smooth w on interior, finite physical time horizon and true finite predictable/product measures, and any epsilon>0, select a genuine compact C2 band 0<u,u+δ<v<Cband with v<Ccap and 0<η<1 and three integers k,j,n such that the original preterminal reserve spends at most epsilon in the shrinking positive lower strip and at most epsilon in the upper cap strip, while original stopped predictable nonlinear C2 Taylor negative-mark L1, L2 and generator-integrand full-to-tail discrepancy all shrink below epsilon at a common mark cutoff n. Combines independently Proved actual compact C2 existence, real reserve product/spatial occupation and true Lévy ν mark source. This is a source-localisation package for the original purejump Ito proof, not a claim of the missing physical-grid martingale identity.
-- source:
--   Proved 79948fba original compact band and η, 2ed57b78 original finitecap true simultaneous two spatial boundary strips and three negative mark cutoff channels. True X,D and σ=0 source retained.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_true_original_existential_spatial_C2_and_threechannel_mark_L1L2_localisation_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (T : ℝ≥0)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (hBV : ¬ X.BoundedVariation)
    (Ccap : ℝ≥0∞) (hCcap : 0 < Ccap)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Ccap})
    (hCfinite : Ccap ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ Ccap)
    (hDcap : IsAdmissibleLe X x Ccap D)
    (N : ℕ) (hN : 0 < N)
    (μsp : Measure (ℝ≥0 × Ω)) [IsFiniteMeasure μsp] :
    ∀ ε : ℝ, 0 < ε →
      ∃ Cband u v δ η : ℝ,
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
        0 < u ∧ 0 < δ ∧ δ ≤ 1 ∧ u + δ < v ∧
        0 < η ∧ η < 1 ∧ v < Cband ∧ v < Ccap.toReal ∧
        ContDiffOn ℝ 2 w (Ioo 0 Cband) ∧
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
