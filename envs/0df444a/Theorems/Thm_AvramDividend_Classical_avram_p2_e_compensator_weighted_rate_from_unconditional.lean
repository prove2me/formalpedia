-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_rate_from_unconditional
-- name    : AvramDividend.Classical.avram_p2_e_compensator_weighted_rate_from_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:53:36.553176+00:00
-- url     : https://prove2.me/theorems/e13617a2-133c-46f4-ba81-94282d26612e
-- title:
--   Weighted original jump compensator from separately proved unconditional Lévy measure rate
-- statement:
--   For the actual original jump count N_X((s,t]×B), an arbitrary nonnegative F_s-measurable past weight W satisfies E[W N] = E[W] (t-s)ν(B), provided the separate unconditional original-process rate E[N]=(t-s)ν(B) has independently been established. No predictable compensator conclusion is assumed as an input. This lemma isolates exactly the deterministic rate dependency owned by P2-D; once that rate is Proved, it yields the weighted predictable-rectangle identity for any such W, including the event indicator used by the canonical compensator.
-- source:
--   Proved/awaiting accepted P2-E original weighted intrinsic rectangle factor 75e37892-da13-48e5-a2ad-9b320ab9045c. P2-D original unconditional rates 859bf7be and d9b9e3c2 are Open until source proof. Parent 393b03a8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_weighted_rate_from_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W)
    (hRate :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω, W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      (∫⁻ ω, W ω ∂P) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
