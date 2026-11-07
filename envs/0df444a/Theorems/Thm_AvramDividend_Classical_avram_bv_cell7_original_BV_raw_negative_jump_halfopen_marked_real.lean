-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_raw_negative_jump_halfopen_marked_real
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_raw_negative_jump_halfopen_marked_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:23:36.93251+00:00
-- url     : https://prove2.me/theorems/5d4e3179-4b17-4e7b-8965-61ddeb5f2837
-- title:
--   Original BV raw negative-jump real sum equals its intrinsic half-open marked integral
-- statement:
--   The actual original bounded-variation Lévy process has pathwise absolutely summable raw negative jumps. On every original half-open cell the exact real raw sum equals the real intrinsic marked jump integral of minus the actual jump mark, using existing BV summability and intrinsic count-to-tsum certificates.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_signed_jump_count_tsum

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_raw_negative_jump_halfopen_marked_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      let Δ : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      let Nst : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict
          ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc s t)).map
            (fun u : ℝ≥0 => (u, Δ u)))
      (∫⁻ p, ENNReal.ofReal (-p.2) ∂Nst).toReal =
        ∑' u : ℝ≥0,
          if s < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0 := by sorry
