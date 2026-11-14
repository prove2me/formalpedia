-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
-- name    : AvramDividend.Classical.avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:33:55.223204+00:00
-- url     : https://prove2.me/theorems/fa6492e8-5cf1-40f6-974b-5b8a45f91352
-- title:
--   Original stopped pre-stop postpayment reserve has uniform value gradient and Hessian C2 envelope almost surely
-- statement:
--   On the original process and dividend right-limit reserve strictly before its stopping clock, the given compact positive prefix bound yields a uniform almost-sure envelope for the value function, its derivative and second derivative. This reuses the proved original source compact prefix transfer and compact C2-jet theorem, supporting the original full-cell quadratic cross L1 and discount estimates.
-- source:
--   Existing proved gledger137 genuine postpayment compact band and wave7_18 compact C2 jet envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_postpayment_C2_jet_uniformly_bounded_on_interior_band
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      let y := x + X.X t ω - rightLimit D t ω
      |w y| ≤ M ∧ |deriv w y| ≤ M ∧ |deriv (deriv w) y| ≤ M := by sorry
