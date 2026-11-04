-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_pre_source_discounted_HJB_nonpos
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_pre_source_discounted_HJB_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:14:33.722354+00:00
-- url     : https://prove2.me/theorems/37d87aff-cd3f-4111-862e-531bd496ef63
-- title:
--   Original BV controlled pre-source reserve has localised discounted HJB jump sign
-- statement:
--   Use the same original spectrally negative Levy process X, filtration, dividend strategy D and source pre-payment left limit Upre defined with rightLimit D. For each omega in a localised event E, conditional only on the source GeneratorIntegrable hypothesis and HJB inequality there, the discounted original physical BV drift plus full negative-jump compensator signed residual is nonpositive. The source model and locality are explicit. No P2 source rate or independent marked process is assumed.
-- source:
--   Original IsDividendStrategy, source pre-state, and the forthcoming P3-B discounted HJB original generator identity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_discounted_HJB_source_jump_residual_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_pre_source_discounted_HJB_nonpos {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (x : ℝ) (w : ℝ → ℝ) (q : ℝ) (s : ℝ≥0) (Upre : Ω → ℝ) (hUpre : ∀ ω, Upre ω = Function.leftLim (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) s) (E : Set Ω) (hGen : ∀ ω ∈ E, X.GeneratorIntegrable w (Upre ω)) (hHJB : ∀ ω ∈ E, X.generator w (Upre ω) - q * w (Upre ω) ≤ 0) : ∀ ω ∈ E, Real.exp (-(q * (s : ℝ))) * (X.drift * deriv w (Upre ω) + (∫ z in Iio (0 : ℝ), w (Upre ω + z) - w (Upre ω) ∂X.ν) - q * w (Upre ω)) ≤ 0 := by sorry
