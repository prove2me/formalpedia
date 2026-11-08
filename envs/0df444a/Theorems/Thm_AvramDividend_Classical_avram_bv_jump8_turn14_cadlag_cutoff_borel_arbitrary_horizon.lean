-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_cadlag_cutoff_borel_arbitrary_horizon
-- name    : AvramDividend.Classical.avram_bv_jump8_turn14_cadlag_cutoff_borel_arbitrary_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:34:15.462214+00:00
-- url     : https://prove2.me/theorems/183b9b2e-14a0-4227-8032-169eca181710
-- title:
--   Càdlàg intrinsic negative-mark cutoff Laplace weight is Borel at any nonnegative horizon
-- statement:
--   For any cutoff k and arbitrary nonnegative horizon T, there is a bounded Borel functional of each real càdlàg path Y equal to the exponential of minus the original intrinsic marked-jump negative-cutoff weighted integral on (0,T]. This generalises the proved unit-horizon result dbbe3fca and can be composed with fractional-length Lévy increment paths.
-- source:
--   Direct parameter-generalisation of Proved dbbe3fca via the already generic Proved b50e56f2 cadlag_mark_weight_lintegral_borel T g hg, preserving the strict negative mark test and real exp bounds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn14_cadlag_cutoff_borel_arbitrary_horizon
    (T : ℝ≥0) (k : ℕ) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ,
      Measurable F ∧ (∀ f, 0 ≤ F f ∧ F f ≤ 1) ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        F Y = Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
          if 0 < p.1 ∧ p.1 ≤ T ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2)
          else 0 ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
            (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u)))).toReal)) := by sorry
