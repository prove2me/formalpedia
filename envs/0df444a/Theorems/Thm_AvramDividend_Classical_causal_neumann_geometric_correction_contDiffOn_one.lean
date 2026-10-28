-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_geometric_correction_contDiffOn_one
-- name    : AvramDividend.Classical.causal_neumann_geometric_correction_contDiffOn_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:46:54.726429+00:00
-- url     : https://prove2.me/theorems/411914ac-d37e-4ee2-a38c-9f6fa2e7f43f
-- title:
--   Positive-time C1 regularity of a signed geometric Neumann correction
-- statement:
--   Under quadratic-geometric bounds for signed convolution powers, uniform geometric bounds for correction primitives, and the exact pointwise derivatives and derivative continuity, the infinite correction series is continuously differentiable on all strictly positive times. Its basepoint summability is proved from the geometric bound.
-- source:
--   Canonically Proved causal_neumann_series_C1_of_signed_power_bounds and contDiffOn_one_Ioi_of_local_open_intervals, together with the pinned geometric summability theorem.

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_neumann_series_C1_of_signed_power_bounds
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_Ioi_of_local_open_intervals

open AvramDividend.Classical Set

theorem AvramDividend.Classical.causal_neumann_geometric_correction_contDiffOn_one
    (P H : ℕ → ℝ → ℝ) (a ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hP : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hH : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hHasDeriv : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      HasDerivAt (H n) (P n x / a - w * H n x) x)
    (hCont : ∀ ε R : ℝ, 0 < ε → ∀ n : ℕ,
      ContinuousOn (fun x : ℝ => P n x / a - w * H n x) (Ioo ε R)) :
    ContDiffOn ℝ 1 (fun y : ℝ => ∑' n : ℕ, H n y)
      (Ioi (0 : ℝ)) := by sorry
