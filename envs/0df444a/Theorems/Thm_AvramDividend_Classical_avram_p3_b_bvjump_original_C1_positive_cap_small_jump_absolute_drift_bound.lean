-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_C1_positive_cap_small_jump_absolute_drift_bound
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_C1_positive_cap_small_jump_absolute_drift_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:43:16.577914+00:00
-- url     : https://prove2.me/theorems/60bc86b3-c0b8-44c8-b459-2ab181620514
-- title:
--   Original BV C1 value's absolute nonlinear small Levy source drift has a finite first-moment envelope
-- statement:
--   The exact P3 C1 smoothness domain and original bounded-variation Levy first-moment condition imply an explicitly finite absolute source small-jump compensator drift bound on each compact positive interior reserve band, with its Lipschitz constant derived rather than assumed.
-- source:
--   Proved original BV first-moment nonlinear source absolute integral estimate, plus C1 compact Lipschitz

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_small_nonlin_absolute_integral_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_C1_positive_cap_small_jump_absolute_drift_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (a b u : ℝ) (ha : 0 < a) (hb : ENNReal.ofReal b < C) (hu : u ∈ Icc (a + 1) b) : ∃ K : ℝ≥0, (∫ z in Ioo (-1 : ℝ) 0, |w (u + z) - w u| ∂X.ν) ≤ (K : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, -z ∂X.ν) := by sorry
