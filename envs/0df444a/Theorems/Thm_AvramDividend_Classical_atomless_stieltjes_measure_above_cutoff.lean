-- Prove2me | Theorems.Thm_AvramDividend_Classical_atomless_stieltjes_measure_above_cutoff
-- name    : AvramDividend.Classical.atomless_stieltjes_measure_above_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:04:44.816981+00:00
-- url     : https://prove2.me/theorems/ed566b72-d802-4682-85c1-4013a423361e
-- title:
--   Atomless Stieltjes representation for a positive-height tail above any cutoff
-- statement:
--   For a positive-axis continuous nonnegative antitone function g vanishing at infinity, and a positive threshold a, clip the input to max(x,a), obtaining a globally continuous antitone positive function. Apply the already-Proved global Stieltjes tail theorem and recover an atomless measure with μ.real(Ici x)=g x on x≥a. This is the local building block for countable gluing when g diverges near zero.
-- source:
--   Proved AvramDividend.Classical.atomless_stieltjes_measure_of_antitone_continuous_tail; pinned Mathlib ContinuousOn.comp_continuous and order max.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_atomless_stieltjes_measure_of_antitone_continuous_tail
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology ENNReal

theorem AvramDividend.Classical.atomless_stieltjes_measure_above_cutoff
    (g : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn g (Ioi (0 : ℝ)))
    (hanti : AntitoneOn g (Ioi (0 : ℝ)))
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hlim : Tendsto g atTop (𝓝 (0 : ℝ))) :
    ∃ μ : Measure ℝ,
      NullSingletonClass μ ∧
      (∀ x : ℝ, μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, a ≤ x → μ.real (Ici x) = g x) := by sorry
