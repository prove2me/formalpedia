-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_negative_smallmark_two_energy_cutoff_epsilon
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_negative_smallmark_two_energy_cutoff_epsilon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:33:36.356705+00:00
-- url     : https://prove2.me/theorems/f66ef7ea-e29e-4595-83d2-ca86b6f7c4e5
-- title:
--   One genuine negative-mark cutoff jointly makes original ruin-stopped nonlinear Taylor L1 and squared tail energies small
-- statement:
--   For the actual prepayment left-limit original controlled reserve, the exact negative Lévy nonlinear Taylor kernel, and any finite predictable physical clock measure, choose a single cutoff index n such that both integrated absolute Taylor remainder and integrated squared remainder are below epsilon. This quantifies the two simultaneous truncation errors needed for the physical Ito stochastic source.
-- source:
--   Public Proved decd1b90 actual full negative C2 stopped Taylor L1/L2 tail tendsto zero and eventually_lt_nhds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_L1_L2_tendsto_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_negative_smallmark_two_energy_cutoff_epsilon
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
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
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
    ∀ ε : ℝ, 0 < ε →
    ∃ n : ℕ,
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) <
        ENNReal.ofReal ε ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ) <
        ENNReal.ofReal ε := by sorry
