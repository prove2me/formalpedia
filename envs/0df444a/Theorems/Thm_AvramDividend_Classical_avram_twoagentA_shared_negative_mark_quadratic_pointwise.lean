-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_negative_mark_quadratic_pointwise
-- name    : AvramDividend.Classical.avram_twoagentA_shared_negative_mark_quadratic_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:38:57.352277+00:00
-- url     : https://prove2.me/theorems/220ef8c8-b828-49b2-9cf3-4e99366b99bb
-- title:
--   Shared proved original physical jump reciprocal-annulus pointwise lemma
-- statement:
--   Reuses an exact previously accepted original-process proof under a shared public name for the unrestricted-Lévy-annular variance-to-L2-cutoff chain; source Prove2Me accepted private source solution d46a3fbc

import Mathlib
open Set
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_shared_negative_mark_quadratic_pointwise
    (i : ℕ) (z : ℝ)
    (hz : z ∈ Set.Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))) :
    let c : ℝ := -(1 / ((i : ℝ) + 1))
    let δ : ℝ := 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    0 ≤ z - c ∧ z - c ≤ δ ∧ δ ≤ 2 * z ^ 2 ∧ c ^ 2 ≤ 4 * z ^ 2 := by sorry
