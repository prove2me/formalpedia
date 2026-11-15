-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a431_continuous_path_dyadic_square_envelope_transfer
-- name    : AvramDividend.Classical.avram_ga_a431_continuous_path_dyadic_square_envelope_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:02:34.40182+00:00
-- url     : https://prove2.me/theorems/c3d5dd97-c594-4cad-8a59-cfc831ece131
-- title:
--   A continuous path inherits a common quadratic bound from all dyadic grid levels
-- statement:
--   If a continuous real path on nonnegative time has its squared values bounded by the same constant on every dyadic grid for a finite horizon, then every time in the horizon has its squared path value bounded by that constant.
-- source:
--   Continuity and convergence of dyadic grid times, with pointwise finite-supremum bounds and the order closedness of real limits.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a431_continuous_path_dyadic_square_envelope_transfer
    {Ω : Type*} (M : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (ω : Ω)
    (hcont : Continuous (fun t : ℝ≥0 => M t ω))
    (S : ℝ)
    (hgrid : ∀ k : ℕ,
      (Finset.range (2^k + 1)).sup' (by simp)
        (fun i => (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2) ≤ S) :
    ∀ t : ℝ≥0, t ≤ T → (M t ω)^2 ≤ S := by sorry
