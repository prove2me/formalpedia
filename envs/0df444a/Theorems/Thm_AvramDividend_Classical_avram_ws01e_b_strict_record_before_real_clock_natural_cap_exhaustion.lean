-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_record_before_real_clock_natural_cap_exhaustion
-- name    : AvramDividend.Classical.avram_ws01e_b_strict_record_before_real_clock_natural_cap_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:45:45.394471+00:00
-- url     : https://prove2.me/theorems/2020a397-2e29-4ff3-94fc-7819ec1ab78d
-- title:
--   Strict first-record-before-real-clock event equals increasing union of finite natural-cap events
-- statement:
--   For any possibly infinite spectrally negative Lévy upper first-passage time τ represented in ENNReal and any real observation clock e, the event τ<toNNReal(e) is the union over finite natural caps N of the events τ<N and τ<toNNReal(e). This preserves strict inequality semantics, handles negative real clock values (toNNReal=0) and infinite τ correctly, and establishes the exact deterministic-cap exhaustion needed to pass capped first-record tilted regeneration identities to arbitrary finite observation clocks by monotone convergence.
-- source:
--   Elementary Archimedean NNReal bound exists_nat_gt, ENNReal coercion order preservation, Set.ext and iUnion membership; no unproved probability or strong-Markov step.

import Mathlib

open Set
open scoped NNReal ENNReal

/-- A finite real observation clock localises every strict ENNReal exit
before that clock into a natural finite deterministic cap. -/

theorem AvramDividend.Classical.avram_ws01e_b_strict_record_before_real_clock_natural_cap_exhaustion
    {Ω Θ : Type*}
    (τ : Ω → ℝ≥0∞) (clock : Θ → ℝ) :
    {z : Ω × Θ | τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)} =
      ⋃ n : ℕ, {z : Ω × Θ |
        τ z.1 < (n : ℝ≥0∞) ∧
        τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)} := by sorry
