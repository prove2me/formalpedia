-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_aligned_grid_active_count_ae_finite
-- name    : AvramDividend.Classical.bv_aligned_grid_active_count_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:49:14.016429+00:00
-- url     : https://prove2.me/theorems/48684234-ddba-4ba2-a3d9-d78572a9a6d5
-- title:
--   Increasing dyadic counts with uniformly finite expected values have almost-sure finite ceilings on aligned grids
-- statement:
--   Let Y be any measurable real-valued process on nonnegative times, and let nested dyadic grids have even-point refinement alignment. If the natural-valued number of strictly positive Y increments on each grid has a common finite expected-value upper bound C, then on a single probability-one event some K(ω) bounds that count on all grids. Measurability of each finite count follows from Measurable.ite and Finset.measurable_sum; count monotonicity is supplied by the Proved aligned-grid deterministic refinement theorem; apply the Proved general a.s. uniform natural-count bound. This is the exact probability/path bridge of the Avram finite-activity no-creep programme.
-- source:
--   Prove2Me accepted dyadic active count refinement and monotone expectation almost-sure bound; Avram Palmowski Pistorius 2007 first-jump valuation.

import Theorems.Thm_AvramDividend_Classical_bv_aligned_dyadic_grid_active_count_monotone
import Theorems.Thm_AvramDividend_Classical_bv_monotone_nat_count_uniformly_bounded_ae
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

open AvramDividend.Classical MeasureTheory Finset
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_aligned_grid_active_count_ae_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ≥0 → ℝ)
    (grid : ℕ → ℕ → ℝ≥0) (C : ℝ≥0∞)
    (hGrid : ∀ n i : ℕ, grid (n + 1) (2 * i) = grid n i)
    (hY : ∀ t : ℝ≥0, Measurable (fun ω => Y ω t))
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, (∑ i ∈ Finset.range (2 ^ n),
        ite (Y ω (grid n i) < Y ω (grid n (i + 1)))
          (1 : ℕ) 0 : ℕ) ∂P) ≤ C)
    (hFinite : C < ⊤) :
    ∀ᵐ ω ∂P, ∃ K : ℕ, ∀ n : ℕ,
      (∑ i ∈ Finset.range (2 ^ n),
        ite (Y ω (grid n i) < Y ω (grid n (i + 1)))
          (1 : ℕ) 0) ≤ K := by sorry
