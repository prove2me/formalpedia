-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_cell_path_increment_limits
-- name    : AvramDividend.Classical.avram_chat24_uniform_cell_path_increment_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:30:31.926191+00:00
-- url     : https://prove2.me/theorems/6efb0b22-87a9-464c-9d5a-2e4e9730cbf6
-- title:
--   Cadlag path increments on strict-left uniform cells converge to the jump
-- statement:
--   Independent geometric/cadlag prerequisite of pointwise parent a2bf4695-628f-49e6-ac17-bf0b48efe4f2, also usable in jump branch eff78840-bf10-4dc9-a987-78b8e980b923. A selected uniform cell has lower endpoint strictly below t and upper endpoint at least t. Existing accepted left-approach and mesh geometry give lower approach from the left, upper approach from the right, and vanishing mesh width. Composing with the assumed P left limit and the f left/right limits makes d*h minus the cell increment converge to leftLim f(t)-f(t). The statement keeps all needed cell membership, positivity, and one-sided-limit hypotheses. It contains no parent or derivative theorem dependency.

import Mathlib
open MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_uniform_cell_path_increment_limits
    (f P : ℝ≥0 → ℝ) (d y : ℝ) (B t : ℝ≥0)
    (hB : 0 < B) (ht : 0 < t) (k : ℕ → ℕ)
    (hk : ∀ n, k n ∈ Finset.range (n + 1))
    (hcell : ∀ n,
      B * (k n : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) < t ∧
      t ≤ B * ((k n + 1 : ℕ) : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0))
    (hfr : ContinuousWithinAt f (Ici t) t)
    (hfl : ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hP : Tendsto P (𝓝[<] t) (nhds y)) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    Tendsto (fun n => u n (k n + 1)) atTop (𝓝[≥] t) ∧
      Tendsto h atTop (nhds 0) ∧
      Tendsto (fun n => P (u n (k n))) atTop (nhds y) ∧
      Tendsto (fun n => d * h n - (f (u n (k n + 1)) - f (u n (k n))))
        atTop (nhds (Function.leftLim f t - f t)) := by sorry
