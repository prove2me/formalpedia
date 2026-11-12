-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger157_original_postpayment_compact_generator_uniform_pointwise_abs_bound
-- name    : AvramDividend.Classical.avram_gledger157_original_postpayment_compact_generator_uniform_pointwise_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:28:29.674196+00:00
-- url     : https://prove2.me/theorems/8c6e383c-db23-42a9-9b7c-76871be7c005
-- title:
--   Original postpayment Gaussian generator residual uniformly bounded on compact pre-stop prefix
-- statement:
--   For the actual original zero-jump stopped Lévy path and genuine dividend rightLimit, the compact strict pre-stop reserve band bounds the full Gaussian generator minus q times w uniformly by one deterministic real constant. Uses the Proved original postpayment compact-band transfer, actual C² jets and zero-jump generator identity; this is the source-specific finite-cell input for gledger155 and gledger153.
-- source:
--   Proved gledger137 original source band, wave7 uniform C2 original postpayment jets, and gledger156 zerojump generator absolute bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger157_original_postpayment_compact_generator_uniform_pointwise_abs_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation)
    (hSigmaNonzero : X.σ ≠ 0) (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      |X.generator w (x + X.X t ω - rightLimit D t ω) -
        q * w (x + X.X t ω - rightLimit D t ω)| ≤ B := by sorry
