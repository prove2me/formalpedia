-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_nested_C2_supclock_discount_predictable_L2
-- name    : AvramDividend.Classical.avram_wave7_18_original_nested_C2_supclock_discount_predictable_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:24:11.493323+00:00
-- url     : https://prove2.me/theorems/738bff35-05f0-424d-a07b-8aa5c3dd1066
-- title:
--   Original nested positive-interior supremum clock has bounded predictable discounted survival weight and finite quadratic energy
-- statement:
--   For the same original spectrally negative Levy source X and dividend strategy D, let tau_n be the nested first dense-grid postpayment-reserve exits from positive C2 bands, cut at deterministic bounded B_n, and let tauSup be their pointwise supremum. The proved exact-domain source theorem makes tauSup a stopping time for the right-continuous original filtration. The proved original-filtration random-stopping discount theorem then makes a(t,omega)=1_{t<=T}exp(-qt)1_{t<=tauSup(omega)} predictable-measurable, bounded in absolute value by one, and zero after T, for q>=0. Against any finite predictable measure its squared lintegral is finite by domination by the constant one. This uses inclusive stopping, and avoids asserting that the exclusive indicator at a jump time is predictable. No unconditional identification with actual ruinTime is made.

import Mathlib
import Mathlib.Probability.Process.Predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_nested_C2_supremum_clock_is_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_nested_C2_supclock_discount_predictable_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0) (hdense : DenseRange r)
    (lower upper : ℕ → ℝ) (B : ℕ → ℝ≥0)
    (hlower : ∀ n, 0 < lower n)
    (hlo : ∀ n, lower (n + 1) ≤ lower n)
    (hup : ∀ n, upper n ≤ upper (n + 1))
    (hcap : ∀ n, ∀ y ∈ Set.Icc (lower n) (upper n), ENNReal.ofReal y < C)
    (hB : ∀ n, B n ≤ B (n + 1))
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let τ : Ω → WithTop ℝ≥0 := fun ω => ⨆ n : ℕ,
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower n ∨
            upper n < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B n : WithTop ℝ≥0)
    let a : ℝ≥0 × Ω → ℝ := fun p =>
      (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
        (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0)
    Measurable[𝓕.rightCont.predictable] a ∧
      (∀ p, |a p| ≤ (1 : ℝ)) ∧
      (∀ p, T < p.1 → a p = 0) ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((a p) ^ 2) ∂μ) < ⊤ := by sorry
