-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn12_original_loss_closed_count_domination
-- name    : AvramDividend.Classical.avram_bv_jump8_turn12_original_loss_closed_count_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:31:19.677064+00:00
-- url     : https://prove2.me/theorems/2152fa92-cb79-4e4b-94a0-b41af9f49093
-- title:
--   Original strictly negative finite exponential loss is bounded by the integrable closed marked count
-- statement:
--   Every strict negative exponential loss lies in [0,1] and the strict selected original time set is a subset of the closed cutoff original set. Thus original loss is bounded pathwise by the nonnegative closed intrinsic marked count, whose L1 integrability was already Proved as 3d8bb7f8.
-- source:
--   Finite strict-original exponential losses are bounded termwise by one; use Proved b34d2b11 cardinal comparison, source closed count ncard/intrinsic identification, and original closed cutoff L1 theorem 3d8bb7f8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_strict_finite_set_card_le_closed
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn12_original_loss_closed_count_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1))))
    ∀ ω : Ω, 0 ≤ L ω ∧ L ω ≤ (N ω).toReal := by sorry
