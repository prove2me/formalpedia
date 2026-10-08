-- Prove2me | Theorems.Thm_AvramDividend_Classical_atomless_positive_tail_measure_of_antitone_continuous
-- name    : AvramDividend.Classical.atomless_positive_tail_measure_of_antitone_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:11:04.555356+00:00
-- url     : https://prove2.me/theorems/c2cc29c2-8fa2-449c-98bc-596566a2bffb
-- title:
--   Atomless locally finite positive-height measure from an antitone continuous tail
-- statement:
--   Construct an atomless measure with finite positive upper tails representing a continuous nonnegative decreasing positive-axis tail tending to zero at infinity, with no assumption of finite total mass. Push the Stieltjes measure for t↦g(exp t) forward under Real.exp.
-- source:
--   Proved global Stieltjes tail theorem and pinned Mathlib Measure.map_apply, exp/log lemmas.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_atomless_stieltjes_measure_of_antitone_continuous_tail
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology ENNReal

theorem AvramDividend.Classical.atomless_positive_tail_measure_of_antitone_continuous
    (g : ℝ → ℝ)
    (hcont : ContinuousOn g (Ioi (0 : ℝ)))
    (hanti : AntitoneOn g (Ioi (0 : ℝ)))
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hlim : Tendsto g atTop (𝓝 (0 : ℝ))) :
    ∃ μ : Measure ℝ,
      NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → μ.real (Ici x) = g x) := by sorry
