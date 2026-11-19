-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finite_range_positive_clock_fullmark_signed_ito_cash_budget
-- name    : AvramDividend.Classical.avram_ja18_original_finite_range_positive_clock_fullmark_signed_ito_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:54:26.691553+00:00
-- url     : https://prove2.me/theorems/0937c152-8869-4252-a4ea-4357d5f0c931
-- title:
--   Original full compensated mark signed Ito inequality implies exact positive-clock conditional cash upper budget
-- statement:
--   At a bounded finite-range original right-continuous stopped clock, the positive-clock set is measurable in the initial filtration. Therefore the genuine fullmark two-noise signed Ito inequality F <= initial value + Gaussian stopped gain + all-negative-jump stopped gain + nonpositive remainder yields the exact original positive-clock masked expected cash budget. This combines the physical finite-range source constructor and Proved initial-event budget, and avoids losing positive clock restrictions or large marks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finite_range_fullmark_signed_ito_initial_event_budget
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_finite_range_positive_clock_fullmark_signed_ito_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (b : ℝ) (hb : 0 ≤ b)
    (hIto : ∀ (R Jsmall Jfull : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (nhds (R t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω + avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          (t : ℝ) * (X.c - ∫ ω, X.X 1 ω ∂P)) →
      ∃ B : Ω → ℝ,
        (∀ᵐ ω ∂(P.restrict (A ∩ {ω : Ω | τ ω ≠ 0})), B ω ≤ 0) ∧
        (∀ᵐ ω ∂(P.restrict (A ∩ {ω : Ω | τ ω ≠ 0})),
          F ω ≤ b + R (τ ω) ω + Jfull (τ ω) ω + B ω)) :
    (∫ ω in A ∩ {η : Ω | τ η ≠ 0}, F ω ∂P) ≤
      b * (P (A ∩ {η : Ω | τ η ≠ 0})).toReal := by sorry
