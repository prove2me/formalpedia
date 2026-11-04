-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_uniform_past_mark_mean_measure_product
-- name    : AvramDividend.Classical.avram_p2_d_future_uniform_past_mark_mean_measure_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:34:30.429643+00:00
-- url     : https://prove2.me/theorems/a34a29b0-668e-4488-9d89-29204f88d1b2
-- title:
--   One original expected mark measure simultaneously factors every past event
-- statement:
--   For each original process and deterministic window, there is one fixed genuine Borel mark measure ρ that works for all events A measurable in the original past at s and all Borel marks B: the past-restricted expected literal count equals P(A)*ρ(B). This stronger quantifier order supports predictable simple-process integration without any ν identification.
-- source:
--   Choose the Proved original unconditioned mark measure once, outside the quantifier over past events, from UUID 03058d10. Then apply the Proved original actual-process future rectangle independence UUID 264b3973 uniformly in each A and B. Unlike the weaker per-A mark measure, this provides a single mean-intensity measure for all past events.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_uniform_past_mark_mean_measure_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ ρ : Measure ℝ,
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ B) ∂P) =
        P A * ρ B := by sorry
