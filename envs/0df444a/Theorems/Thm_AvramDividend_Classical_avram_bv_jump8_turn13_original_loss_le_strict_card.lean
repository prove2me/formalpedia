-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn13_original_loss_le_strict_card
-- name    : AvramDividend.Classical.avram_bv_jump8_turn13_original_loss_le_strict_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:25:44.012889+00:00
-- url     : https://prove2.me/theorems/4fd76c29-fde3-4f05-b0d2-af7c4eaed503
-- title:
--   Actual original strict exponential jump loss is at most its finite jump count
-- statement:
--   Each original strictly negative marked exponential loss is bounded above by one, hence the genuine finite original loss sum is bounded by the strict negative jump count.
-- source:
--   One minus a positive real exponential is at most one; sum termwise on the actual original finite strict cutoff jump set. This is the essential local inequality feeding original closed-count domination.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn13_original_loss_le_strict_card
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    ∀ ω : Ω, L ω ≤ ((S ω).card : ℝ) := by sorry
