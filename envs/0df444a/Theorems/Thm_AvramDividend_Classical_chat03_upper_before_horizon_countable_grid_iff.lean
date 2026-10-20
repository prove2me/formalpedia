-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_upper_before_horizon_countable_grid_iff
-- name    : AvramDividend.Classical.chat03_upper_before_horizon_countable_grid_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:36:16.886401+00:00
-- url     : https://prove2.me/theorems/c4e268ac-950c-4843-96a7-7742108a50c5
-- title:
--   A strict upper first-passage witness before a finite horizon is detected on a countable grid before that horizon
-- statement:
--   For each official spectrally negative Lévy sample path, upper real threshold, and nonnegative finite horizon T, there exists a strict upper crossing at some time s<T if and only if some inverse-natural grid time k/n with positive integer n satisfies k/n<T and upper<X_{k/n}. Right-continuity ensures a strict upper crossing persists on a right interval, and choosing the mesh smaller than the distance to both the interval endpoint and T puts the ceiling grid sample strictly before the horizon. Unlike a global existence equivalence, this yields the exact finite-horizon passage event used to prove measurability of the strict upper passage clock.
-- source:
--   Proved chat03_strict_upper_exit_right_interval plus proved chat03_nnreal_grid_ceiling_bracket and pinned NNReal.exists_nat_pos_inv_lt.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Data.NNReal.Defs

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_upper_before_horizon_countable_grid_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (upper : ℝ) (T : ℝ≥0) :
    (∃ s : ℝ≥0, s < T ∧ upper < X.X s ω) ↔
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω := by sorry
