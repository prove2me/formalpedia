-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_smallmark_explicit_eta_joint_L1_L2_epsilon
-- name    : AvramDividend.Classical.avram_pj_workerC_original_smallmark_explicit_eta_joint_L1_L2_epsilon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:38:04.794401+00:00
-- url     : https://prove2.me/theorems/dc2aade1-539b-4f30-8d06-d9762621f880
-- title:
--   For one explicit shrinking negative jump cutoff eta_n, original stopped nonlinear Taylor absolute and square energies both below epsilon
-- statement:
--   Under the exact true controlled Lévy reserve and finite physical predictable clock measure, a positive antitone cutoff eta_n tending to zero yields some n such that actual stopped nonlinear C2 jump remainder on (-eta_n,0) has both integrated absolute and squared tail energies below epsilon. This is the concrete marked cutoff selection needed to handle the joint first-order and nonlinear physical Ito errors.
-- source:
--   Proved decd1b90 full stopped negative C2 tail; newly separated mark-family nesting and single-index two-energy threshold lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_smallmark_explicit_eta_joint_L1_L2_epsilon
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
    (eta : ℕ → ℝ) (hpos : ∀ n, 0 < eta n)
    (hanti : Antitone eta)
    (hlim : Tendsto eta atTop (𝓝 (0 : ℝ))) :
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
          ∫⁻ z in Ioo (-eta n) (0 : ℝ),
            ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) < ENNReal.ofReal ε ∧
        (∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in Ioo (-eta n) (0 : ℝ),
            ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ) <
          ENNReal.ofReal ε := by sorry
