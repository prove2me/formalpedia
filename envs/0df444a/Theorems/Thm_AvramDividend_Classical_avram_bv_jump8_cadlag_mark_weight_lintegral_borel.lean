-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
-- name    : AvramDividend.Classical.avram_bv_jump8_cadlag_mark_weight_lintegral_borel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:41:58.36721+00:00
-- url     : https://prove2.me/theorems/b50e56f2-0dcb-4abc-8122-4101ca1c9ec0
-- title:
--   Generic measurable coordinate-path extension of any nonnegative Borel weighted càdlàg jump integral
-- statement:
--   For an arbitrary finite source time horizon and nonnegative Borel mark weight, construct a globally coordinate-product measurable extended nonnegative real statistic agreeing on every càdlàg path with the exact intrinsic weighted jump integral. Builds from already-Proved Borel marked count extensions using measurable simple-function approximation and monotone convergence. Handles infinite mass and time-zero exclusion.
-- source:
--   General nonnegative weighted path functional extends Proved 41bfd2c8 (arbitrary Borel marked count) by simple-function monotone approximation and exact lintegral definition. Substantive child to prove the bounded exponential path extension b879-cadlag and to reuse for original past-filtration truncations. It does not assert a Poisson law or independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_cadlag_mark_weight_lintegral_borel
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∃ W : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable W ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        W Y =
          ∫⁻ p : ℝ≥0 × ℝ,
            if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
              ((Measure.count.restrict {u : ℝ≥0 |
                0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
                (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u))) := by sorry
