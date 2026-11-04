-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_pre_source_integrable_HJB_expected_nonpos
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_pre_source_integrable_HJB_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:22:05.68726+00:00
-- url     : https://prove2.me/theorems/1d6ba5ec-b7a7-4423-b0e9-9eacfce75aa5
-- title:
--   Original controlled BV pre-source localised HJB residual has nonpositive expectation
-- statement:
--   On the same original source process, filtration and actual controlled dividend reserve pre-source state, a localised L1 HJB signed residual has nonpositive expectation. The residual is explicitly the physical BV drift, the original source negative-jump generator compensator, and discount term on E, with zero outside E. The theorem assumes actual Integrable F P, so no unsupported optional stopping or expectation is used. It is independent of P2; the original stochastic jump compensation is separate.
-- source:
--   Mathlib MeasureTheory.integral_nonpos_of_ae and the P3-B original controlled pre-source discounted HJB helper

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_pre_source_discounted_HJB_nonpos
open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_pre_source_integrable_HJB_expected_nonpos {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (x : ℝ) (w : ℝ → ℝ) (q : ℝ) (s : ℝ≥0) (Upre : Ω → ℝ) (hUpre : ∀ ω, Upre ω = Function.leftLim (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) s) (E : Set Ω) (hGen : ∀ ω ∈ E, X.GeneratorIntegrable w (Upre ω)) (hHJB : ∀ ω ∈ E, X.generator w (Upre ω) - q * w (Upre ω) ≤ 0) (F : Ω → ℝ) (hF : ∀ ω ∈ E, F ω = Real.exp (-(q * (s : ℝ))) * (X.drift * deriv w (Upre ω) + (∫ z in Iio (0 : ℝ), w (Upre ω + z) - w (Upre ω) ∂X.ν) - q * w (Upre ω))) (hFzero : ∀ ω ∉ E, F ω = 0) (hFint : Integrable F P) : (∫ ω, F ω ∂P) ≤ 0 := by sorry
