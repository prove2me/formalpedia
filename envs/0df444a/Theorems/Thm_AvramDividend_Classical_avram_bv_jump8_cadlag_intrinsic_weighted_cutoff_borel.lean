-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_intrinsic_weighted_cutoff_borel
-- name    : AvramDividend.Classical.avram_bv_jump8_cadlag_intrinsic_weighted_cutoff_borel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T18:50:21.778828+00:00
-- url     : https://prove2.me/theorems/dbbe3fca-38c2-430c-bfa8-3eb481394d59
-- title:
--   Cadlag intrinsic strict-cutoff marked magnitude Laplace weight has bounded coordinate-measurable extension
-- statement:
--   For any càdlàg real path, the exponential of its true weighted negative marked-jump integral over (0,1] agrees with a globally coordinate-product measurable [0,1]-valued functional. Construct through measurable arbitrary-Borel jump-count extractors and bounded monotone simple-mark approximations, including infinite jump mass.
-- source:
--   Mathematical child of b879a7b0. Generalise Proved 41bfd2c8 arbitrary Borel càdlàg jump-count extension from indicator marks to weighted magnitude via dyadic nonnegative simple functions and lintegral monotone convergence. Preserve ENNReal.toReal convention at infinity and time-zero exclusion. Repair of terminal publication job b92463b1-d203-4695-9359-887464174f08: add missing defining Avram module and Topology opened namespace; exact mathematical proposition unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_cadlag_intrinsic_weighted_cutoff_borel
    (k : ℕ) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ,
      Measurable F ∧ (∀ f, 0 ≤ F f ∧ F f ≤ 1) ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        F Y = Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
          if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
            (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u)))).toReal)) := by sorry
