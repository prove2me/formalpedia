-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finite_range_positive_clock_fullmark_upper_implies_budget
-- name    : AvramDividend.Classical.avram_ja18_original_finite_range_positive_clock_fullmark_upper_implies_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:54:36.413694+00:00
-- url     : https://prove2.me/theorems/2f10dda7-6f3f-4ba1-a33a-dd441a1e6dc6
-- title:
--   Original positive-clock physical Gaussian and all-mark upper inequality implies full cash budget
-- statement:
--   For original finite-activity Lévy and exact full Stieltjes ruinclipped reward at a bounded finite-range stopping clock, an almost-sure physical upper inequality F<=w(x)+R(tau)+Jfull(tau) on the positive-clock initial event implies the eventwise expected reward bound. This uses Proved original physical Gaussian and complete-negative-mark stopped gains, each with zero expectation on positive-clock initial events. It avoids any extra assumption w(x)>=0 and retains all large negative jumps, reducing the budget to the single signed Ito cash inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finite_range_positive_clock_two_fullmark_noises_centered
import Theorems.Thm_AvramDividend_Classical_avram_b21_initial_event_local_aggregate_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_finite_range_positive_clock_fullmark_upper_implies_budget
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
    (hSigned : ∀ (R Jsmall Jfull : ℝ≥0 → Ω → ℝ),
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
      ∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | τ η ≠ 0})),
        F ω ≤ w x + R (τ ω) ω + Jfull (τ ω) ω) :
    (∫ ω in A ∩ {η : Ω | τ η ≠ 0}, F ω ∂P) ≤
      w x * (P (A ∩ {η : Ω | τ η ≠ 0})).toReal := by sorry
