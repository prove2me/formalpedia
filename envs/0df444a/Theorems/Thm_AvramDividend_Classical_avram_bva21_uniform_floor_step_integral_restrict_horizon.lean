-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva21_uniform_floor_step_integral_restrict_horizon
-- name    : AvramDividend.Classical.avram_bva21_uniform_floor_step_integral_restrict_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:01:38.192124+00:00
-- url     : https://prove2.me/theorems/fcd068c1-9686-4984-b119-73a4d7f031b7
-- title:
--   Original uniform floor-step integral is supported inside the physical finite horizon
-- statement:
--   The exact original uniform floor-step compensator integrand is supported on the strict inner horizon [0,T(n+1)/(n+2)), a subset of the physical finite horizon [0,T]. Consequently its integral over the full real line equals integration over the finite Lebesgue restriction. Combined with Proved B21 step-sum and floor-mask identities, this places the source-A integral in the same measure as source-K for the paired dominated convergence proof of 7ccc2a1a.
-- source:
--   Exact finite-horizon source-A integral restriction required to apply paired DCT to original 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bva21_uniform_floor_step_integral_restrict_horizon
    (T : ℝ) (hT : 0 < T) (n : ℕ) (c : ℕ → ℝ) :
    (∫ t : ℝ,
      if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0) =
    ∫ t in Set.Icc (0 : ℝ) T,
      if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0 := by sorry
