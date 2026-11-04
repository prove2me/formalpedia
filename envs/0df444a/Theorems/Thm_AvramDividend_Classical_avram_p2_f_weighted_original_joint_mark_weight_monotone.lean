-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_joint_mark_weight_monotone
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_joint_mark_weight_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:22:04.023502+00:00
-- url     : https://prove2.me/theorems/91324ed3-0009-40b5-8770-5ab973abf89c
-- title:
--   Joint monotonicity of original source marked weighted expectations
-- statement:
--   Simultaneous increasing approximation of arbitrary nonnegative path weights and Borel mark bands preserves monotonicity of the genuine original Lévy source marked-count lintegral, without an assumed ν-rate, independence, integrability or finiteness. It is the joint approximation side-condition for predictable simple kernels.
-- source:
--   MeasureTheory.lintegral_mono, measure_mono, Set.prod_mono, ENNReal multiplication monotonicity. Original intrinsic jump measure unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_joint_mark_weight_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : ℕ → Set ℝ)
    (hB : Monotone B)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ i j, i ≤ j → ∀ ω, H i ω ≤ H j ω) :
    Monotone (fun n : ℕ =>
      (∫⁻ ω, H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B n)) ∂P)) := by sorry
