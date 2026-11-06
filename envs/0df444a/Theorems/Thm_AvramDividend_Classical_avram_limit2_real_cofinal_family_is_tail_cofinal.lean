-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_real_cofinal_family_is_tail_cofinal
-- name    : AvramDividend.Classical.avram_limit2_real_cofinal_family_is_tail_cofinal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:42:49.673924+00:00
-- url     : https://prove2.me/theorems/e21e2c9d-331a-43a7-88e6-3f6eadc41794
-- title:
--   Cofinal real horizon families remain cofinal after every finite prefix
-- statement:
--   A possibly nonmonotone real-valued sequence unbounded above has the tail-cofinal property: for any N and real a, there exists k≥N with T(k)≥a. The finite prefix 0,...,N-1 has a finite upper bound M, and cofinality above max(a,M)+1 forces an index beyond the prefix. This supports vanishing-index error estimates together with arbitrary cofinal closed/strict horizons, preserving original time atoms.

import Mathlib

theorem AvramDividend.Classical.avram_limit2_real_cofinal_family_is_tail_cofinal
    (T : ℕ → ℝ)
    (hCofinal : ∀ a : ℝ, ∃ k : ℕ, a ≤ T k) :
    ∀ (N : ℕ) (a : ℝ), ∃ k : ℕ, N ≤ k ∧ a ≤ T k := by sorry
