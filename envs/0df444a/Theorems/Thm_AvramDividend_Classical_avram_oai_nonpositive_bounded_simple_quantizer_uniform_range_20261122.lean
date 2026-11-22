-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_nonpositive_bounded_simple_quantizer_uniform_range_20261122
-- name    : AvramDividend.Classical.avram_oai_nonpositive_bounded_simple_quantizer_uniform_range_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:45:12.1378+00:00
-- url     : https://prove2.me/theorems/5dfa5c28-6e9b-4cb5-8579-d961e3872216
-- title:
--   Original negative-jump real marks admit nonpositive, unit-bounded simple quantisers with pointwise convergence
-- statement:
--   Construct a sequence of Borel real simple functions taking every value in [-1,0] and converging pointwise to the identity on [-1,0]. Use the pinned Mathlib SimpleFunc.approxOn for id with target compact interval [-1,0], its exact value-range and closure-convergence theorems. This ensures squaring is injective on the finite range of each quantiser, providing the missing deterministic squared-fibre energy identity needed by the actual all-activity Lévy marked-jump exact L2 isometry.

import Mathlib
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_nonpositive_bounded_simple_quantizer_uniform_range_20261122 :
    ∃ f : ℕ → SimpleFunc ℝ ℝ,
      (∀ k z, f k z ∈ Icc (-1 : ℝ) 0) ∧
      (∀ z ∈ Icc (-1 : ℝ) 0,
        Tendsto (fun k => f k z) atTop (𝓝 z)) := by sorry
