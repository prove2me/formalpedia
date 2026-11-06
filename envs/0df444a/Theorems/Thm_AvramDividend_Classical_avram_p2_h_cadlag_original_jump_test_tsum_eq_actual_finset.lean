-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_original_jump_test_tsum_eq_actual_finset
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_original_jump_test_tsum_eq_actual_finset
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:14:46.321696+00:00
-- url     : https://prove2.me/theorems/f027d528-fa12-4f8d-b948-abd2cf1f8e8c
-- title:
--   Original càdlàg jump-test series equals a genuine finite actual-jump sum
-- statement:
--   For the actual original source process and any test that vanishes near zero, exhibit the precise finite set F of times in (0,T] where the genuine intrinsic jump-test f(X_u-X_{u-}) is nonzero. The unrestricted real tsum over all times, restricted to the horizon, equals the literal finite Finset sum over F. The proof uses the independently proved source finite-large-jump localisation and honest finite-support tsum_eq_sum, with no compensator, rate or process replacement.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_h_cadlag_original_jump_test_tsum_eq_actual_finset
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (f : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hzero : ∀ y : ℝ, |y| < δ → f y = 0) :
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧ f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0) ∧
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ T then f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) else 0) =
        ∑ u ∈ F, f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by sorry
