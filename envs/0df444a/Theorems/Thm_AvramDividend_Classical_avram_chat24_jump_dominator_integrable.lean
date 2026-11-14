-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_jump_dominator_integrable
-- name    : AvramDividend.Classical.avram_chat24_jump_dominator_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:47:40.591196+00:00
-- url     : https://prove2.me/theorems/7209fe13-b4be-48a8-8075-72088e7897f6
-- title:
--   Summable downward jumps have an integrable marked dominator
-- statement:
--   Exact first conjunct of jump branch eff78840-bf10-4dc9-a987-78b8e980b923, with only the hypotheses it uses. Right/left regularity gives measurability of f and its left limit. Apply the already accepted mapped jump-cell integral core at s=0,t=B to the measurable jump function Delta=f-leftLim f; summability of -Delta is the supplied jump-mass summability. Restrict its integrable first-moment function to negative marks and multiply by L. This child is independent of the mesh, the payoff w, band/control K, Y, and the parent conclusion.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_jump_dominator_integrable
    (f : ℝ≥0 → ℝ) (B : ℝ≥0) (L : ℝ≥0)
    (hf_right : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hf_left : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hf_down : ∀ t : ℝ≥0, 0 < t → f t ≤ Function.leftLim f t)
    (hsum : Summable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ B then Function.leftLim f t - f t else 0)) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ f u - Function.leftLim f u ≠ 0}).map
        (fun u : ℝ≥0 => (u, f u - Function.leftLim f u)))
    let Jdom : ℝ≥0 × ℝ → ℝ := fun p =>
      if 0 < p.1 ∧ p.1 ≤ B ∧ p.2 < 0 then (L : ℝ) * (-p.2) else 0
    Integrable Jdom NX := by sorry
