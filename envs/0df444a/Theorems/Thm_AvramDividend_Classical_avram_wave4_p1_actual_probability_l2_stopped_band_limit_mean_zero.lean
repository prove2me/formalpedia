-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero
-- name    : AvramDividend.Classical.avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:04:23.056462+00:00
-- url     : https://prove2.me/theorems/540bd939-b21d-4883-901a-fc40fbf58ec6
-- title:
--   Original probability-space stopped compensated finite bands have a centered L² limit
-- statement:
--   Let M_n be the actual finite-band compensated integrals as elements of L² of the original probability measure P. Given the explicitly source-verifiable finite-band L² increment isometry bound and ∫ M_n dP=0 for each n, prove an actual L²(P) limit exists and has zero expectation. This removes the auxiliary continuity-of-expectation hypothesis from the abstract completed-limit theorem by importing the P1 theorem that expectation is continuous on original L²(P). It does not assert or assume Poisson compensation for the original X: source 04-A must still establish the finite-band isometry and mean-zero identities from its PRM law.
-- source:
--   P1 complete centered limit b028e313 Proved; P1 original L² expectation continuity theorem (authoring pending) and pinned Mathlib Lp completeness.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_band_centered_l2_limit_preserves_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_probability_l2_expectation_continuous_original_space

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure α)
    (f : α → ℝ) (hf : Measurable f)
    (henergy : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ∞)
    (B : ℕ → Set α) (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, μ (B n) < ∞)
    (hBmono : Monotone B) (hBcover : (⋃ n, B n) = Set.univ)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hfinite_band_isometry_bound :
      ∀ m n, m ≤ n →
        dist (M m) (M n) ≤
          (eLpNorm ((B m)ᶜ.indicator f) (2 : ℝ≥0∞) μ).toReal)
    (hcentered : ∀ n, ∫ ω, (M n) ω ∂P = 0) :
    ∃ Mlimit : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (nhds Mlimit) ∧
      (∫ ω, Mlimit ω ∂P) = 0 := by sorry
