-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_bounded_real_simple_mark_approx
-- name    : AvramDividend.Classical.avram_a21_bounded_real_simple_mark_approx
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:19:54.692454+00:00
-- url     : https://prove2.me/theorems/d206f112-be65-4441-b042-0a3427c04181
-- title:
--   Bounded Borel-simple mark approximations to the identity on the negative unit interval
-- statement:
--   Construct a sequence of finite-valued measurable real mark functions globally bounded by one, converging at every mark in [-1,0] to that mark. These give the finite Borel-mark partitions required to approximate original compensated jump-strip integrals on the same underlying sample space.
-- source:
--   Prerequisite to the physical Borel-simple energy certificate 67336b2d; supported by Mathlib SimpleFunc.approxOn, approxOn_mem and tendsto_approxOn. No alternate probability space.

import Mathlib
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_bounded_real_simple_mark_approx
    : ∃ (f : ℕ → SimpleFunc ℝ ℝ),
        (∀ k z, |f k z| ≤ 1) ∧
        (∀ z ∈ Icc (-1 : ℝ) 0,
          Tendsto (fun k => f k z) atTop (𝓝 z)) := by sorry
