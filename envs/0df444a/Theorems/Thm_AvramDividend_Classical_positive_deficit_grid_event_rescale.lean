-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_deficit_grid_event_rescale
-- name    : AvramDividend.Classical.positive_deficit_grid_event_rescale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:40:32.836804+00:00
-- url     : https://prove2.me/theorems/70cacc22-ed0c-4442-baa3-ed5c4ecded9e
-- title:
--   Rescale a small-positive drift-deficit grid event by its strictly positive cell count
-- statement:
--   For positive grid count N, the small-positive event 0<D≤b is exactly the event 0<D and N D≤N b. This identifies the event in the uniform-mesh survival inequality with the event controlled by the actual Lévy-process Laplace-minus-zero-atom bound.
-- source:
--   Elementary ordered-field rescaling used in the finite-activity first-jump proof, Avram et al (2007) Section 3.3.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Order.Ring.Defs

theorem AvramDividend.Classical.positive_deficit_grid_event_rescale
    {Ω : Type*} (D : Ω → ℝ) (N : ℕ) (hN : 0 < N) (b : ℝ) :
    {ω : Ω | 0 < D ω ∧ D ω ≤ b} =
      {ω : Ω | 0 < D ω ∧ (N : ℝ) * D ω ≤ (N : ℝ) * b} := by sorry
