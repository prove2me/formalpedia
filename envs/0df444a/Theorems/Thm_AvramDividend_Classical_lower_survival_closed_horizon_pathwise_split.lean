-- Prove2me | Theorems.Thm_AvramDividend_Classical_lower_survival_closed_horizon_pathwise_split
-- name    : AvramDividend.Classical.lower_survival_closed_horizon_pathwise_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:24:38.15138+00:00
-- url     : https://prove2.me/theorems/28d29610-0e96-4de1-b67d-2d9e1dabbb83
-- title:
--   Split continuous lower-barrier survival at any deterministic time
-- statement:
--   For any real-valued path started at reserve x and times s≤u, staying nonnegative over the whole closed interval from zero to u is exactly equivalent to staying nonnegative until s and then surviving over the remaining interval using the reserve at s plus the future increments. This is an exact pathwise event split that supports the one-sided killed Lévy Markov semigroup without any probability or regularity assumptions.
-- source:
--   Pathwise algebraic decomposition of one-sided closed-horizon survival, to be coupled with full-history Lévy Markov–Tonelli and Esscher exponential factorisation. Related to the two-sided exit construction of Avram, Palmowski and Pistorius (2007).

import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

open Set
open scoped NNReal

theorem AvramDividend.Classical.lower_survival_closed_horizon_pathwise_split
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ) (x : ℝ)
    (s u : ℝ≥0) (hsu : s ≤ u) :
    {ω : Ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + Y v ω} =
      {ω : Ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + Y v ω} ∩
      {ω : Ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + Y s ω) + (Y v ω - Y s ω)} := by sorry
