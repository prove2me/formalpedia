-- Prove2me | solution 1 for lonely_runner_conjecture
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:07:37.314277+00:00
-- url     : https://prove2.me/submissions/abec2200-064f-48ac-a877-300ad1e2936e

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution : ¬ (∀ (n : ℕ), 1 ≤ n → ∀ (speeds : Fin n → ℝ),
    (∀ i j : Fin n, i ≠ j → speeds i ≠ speeds j) →
    ∃ t : ℝ, 0 < t ∧ ∀ i : Fin n,
      let pos := Int.fract (speeds i * t)
      (1 : ℝ) / (n + 1) ≤ pos ∧ pos ≤ 1 - 1 / (n + 1)) := by
  intro h
  let speeds : Fin 3 → ℝ := fun i => i.val
  have hinj : ∀ i j : Fin 3, i ≠ j → speeds i ≠ speeds j := by
    intro i j hij heq
    apply hij
    exact Fin.ext (Nat.cast_injective heq)
  obtain ⟨t, _, hpos⟩ := h 3 (by decide) speeds hinj
  have hh := (hpos 0).1
  norm_num [speeds] at hh
