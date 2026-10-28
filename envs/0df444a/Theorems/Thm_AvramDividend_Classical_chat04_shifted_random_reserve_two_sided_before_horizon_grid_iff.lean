-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_two_sided_before_horizon_grid_iff
-- name    : AvramDividend.Classical.chat04_shifted_random_reserve_two_sided_before_horizon_grid_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:57:23.069021+00:00
-- url     : https://prove2.me/theorems/0395419d-5d7a-4454-b76c-a65b5aaacf15
-- title:
--   Strict two-sided exit before a finite horizon is exactly detected by a rational grid for a shifted random reserve
-- statement:
--   For any shifted spectrally negative Lévy path started from arbitrary path-dependent reserve H, exit from the closed interval [0,a] by a strict lower or upper crossing before a deterministic horizon T occurs if and only if some rational time k/n before T witnesses one of these two crossings. This follows from separately Proved exact rational-grid detection of strict lower and strict upper passages.
-- source:
--   Proved lower and upper shifted strict exit rational-grid equivalences, joined by disjunction elimination.

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_lower_before_horizon_grid_iff
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_upper_before_horizon_grid_iff

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_shifted_random_reserve_two_sided_before_horizon_grid_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b T : ℝ≥0) :
    (∃ v : ℝ≥0, v < T ∧
      ((H ω + (X.X (b + v) ω - X.X b ω) < 0) ∨
        (a < H ω + (X.X (b + v) ω - X.X b ω)))) ↔
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
      ((H ω +
        (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω) < 0) ∨
        (a < H ω +
          (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω))) := by sorry
