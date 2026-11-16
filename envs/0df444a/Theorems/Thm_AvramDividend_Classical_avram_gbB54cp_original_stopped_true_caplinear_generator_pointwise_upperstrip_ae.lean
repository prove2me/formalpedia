-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_original_stopped_true_caplinear_generator_pointwise_upperstrip_ae
-- name    : AvramDividend.Classical.avram_gbB54cp_original_stopped_true_caplinear_generator_pointwise_upperstrip_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:25:34.1942+00:00
-- url     : https://prove2.me/theorems/84445bd8-5440-4db2-8f4f-325737261fdd
-- title:
--   Original finite-cap stopped zero-jump Gaussian generator HJB drift bounded pointwise off the upper kink almost everywhere
-- statement:
--   For the actual stopped original postpayment reserve Y=x+X-rightLimit D on the true finite pre-stop real-time window, Lebesgue-a.e. times are in the positive reserve and avoid the upper clipping point b. Therefore the generator-minus-discount of the caplinear potential V_b is bounded pointwise by max(c,0) on the upper strip and by zero elsewhere. This is stronger than a plain integral inequality, supports the original exponential discount weight and uses the true source upper kink/null occupation rather than an auxiliary Brownian model.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB54cp_original_stopped_true_caplinear_generator_pointwise_upperstrip_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (b : ℝ)
    (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ᵐ ω ∂P,
      let S : Set ℝ := {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
      let μ : Measure ℝ := volume.restrict S
      let Y : ℝ → ℝ := fun t =>
        x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
      let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
      ∀ᵐ t ∂μ,
        X.generator V (Y t) - q * V (Y t) ≤
          if b < Y t then max X.c 0 else 0 := by sorry
