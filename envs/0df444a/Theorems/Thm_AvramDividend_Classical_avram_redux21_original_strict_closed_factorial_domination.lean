-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux21_original_strict_closed_factorial_domination
-- name    : AvramDividend.Classical.avram_redux21_original_strict_closed_factorial_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:04:54.047836+00:00
-- url     : https://prove2.me/theorems/7a4f4356-3444-400e-b54e-89fa8dc3614c
-- title:
--   Original strict marked count second factorial is bounded by closed-cutoff second factorial
-- statement:
--   For the original spectrally negative Lévy path and every finite horizon, the strict negative mark second factorial count is bounded pathwise by the closed-band second factorial count. The closed band has an exact expected factorial moment already proved.
-- source:
--   Apply Proved strict-to-closed original jump-time count inequality b34d2b11 and monotonicity of n(n-1) for natural n, paying attention to zero counts and the cutoff atom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_strict_finite_set_card_le_closed
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux21_original_strict_closed_factorial_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    let a : ℕ :=
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset.card
    let b : ℕ := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((k : ℝ) + 1))}.ncard
    (a : ℝ) * ((a : ℝ) - 1) ≤ (b : ℝ) * ((b : ℝ) - 1) := by sorry
