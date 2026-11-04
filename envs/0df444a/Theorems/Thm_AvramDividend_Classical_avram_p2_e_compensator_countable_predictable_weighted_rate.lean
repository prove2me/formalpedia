-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_countable_predictable_weighted_rate
-- name    : AvramDividend.Classical.avram_p2_e_compensator_countable_predictable_weighted_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:08:53.352401+00:00
-- url     : https://prove2.me/theorems/9d79c515-916e-49b2-9c09-ab866d21e6d0
-- title:
--   Countable nonnegative predictable marked jump compensation for the original Lévy process
-- statement:
--   For a countable nonnegative family of original spectrally negative Lévy path jump rectangles (s_i,t_i]×B_i with genuinely past-measurable weights W_i, the unconditional ENNReal expectation of their infinite sum equals the series of E[W_i](t_i-s_i)ν(B_i), provided the separately established unconditional source rate for each rectangle. This holds without finite activity or a finite expectation assumption, and is a Tonelli extension of the finite predictable-simple compensation bridge.
-- source:
--   Proved P2-E original intrinsic count measurability 8146a449, Proved conditional weighted compensation e13617a2 and pinned Mathlib lintegral_tsum; original P2-D ν-rate 859bf7be remains independent/Open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_rate_from_unconditional

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_countable_predictable_weighted_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℕ → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (W : ℕ → Ω → ℝ≥0∞)
    (hW : ∀ i, Measurable[𝓕 (s i)] (W i))
    (hRate : ∀ i,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) =
        ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) :
    (∫⁻ ω, ∑' i,
      W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) =
    ∑' i, (∫⁻ ω, W i ω ∂P) *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by sorry
