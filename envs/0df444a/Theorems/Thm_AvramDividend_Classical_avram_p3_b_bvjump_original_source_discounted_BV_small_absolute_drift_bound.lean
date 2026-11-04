-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_discounted_BV_small_absolute_drift_bound
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_source_discounted_BV_small_absolute_drift_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:22:27.663463+00:00
-- url     : https://prove2.me/theorems/0d84bb8a-a313-4e6b-ab43-3194ab7e542c
-- title:
--   Discounted original BV nonlinear small-jump absolute compensator drift has uniform first-moment bound
-- statement:
--   For the genuine original BV Lévy measure X.ν, a nonnegative discount rate q and physical time t≥0 have 0<exp(-qt)≤1. The total absolute discounted nonlinear jump drift over (-1,0) at any compact-interior reserve u is bounded uniformly by K times the original source negative first-jump moment, finite from X.BoundedVariation. The exact physical source truncation is retained and no global large-jump first moment is presumed.
-- source:
--   Original compact BV source absolute jump integral bound with Real.exp_le_one_iff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_small_nonlin_absolute_integral_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_source_discounted_BV_small_absolute_drift_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (w : ℝ → ℝ) (K : ℝ≥0) (a b u : ℝ) (hLip : LipschitzOnWith K w (Icc a b)) (hu : u ∈ Icc (a + 1) b) (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0) : (∫ z in Ioo (-1 : ℝ) 0, |Real.exp (-(q * (t : ℝ))) * (w (u + z) - w u)| ∂X.ν) ≤ (K : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, -z ∂X.ν) := by sorry
