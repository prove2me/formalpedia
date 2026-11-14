-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB52_original_C1_positive_deriv_bound_to_closed_cap_lipschitz
-- name    : AvramDividend.Classical.avram_bva_capHJB52_original_C1_positive_deriv_bound_to_closed_cap_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:40:14.432537+00:00
-- url     : https://prove2.me/theorems/15ea4205-9cf5-4343-9c87-8d225423c561
-- title:
--   Original positive-reserve C1 derivative bound extends to closed finite-cap Lipschitz estimate
-- statement:
--   For a finite upper dividend cap c and positive lower reserve a, if the actual source dividend candidate is continuous on the closed positive compact interval, differentiable on its open interior and its derivative norm is bounded above by a fixed nonnegative K there, then the candidate is K-Lipschitz on the entire closed interval, including the upper dividend cap. Apply the exact pinned Mathlib convex mean-value Lipschitz theorem on the open band and extension from a dense set to its closure. This is essential for full original negative mark integrability retaining cap occupation, and does not assert any false A22 cofinal spatial-mask positive L1 convergence.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB52_original_C1_positive_deriv_bound_to_closed_cap_lipschitz
    (w : ℝ → ℝ) (a c : ℝ) (ha : a < c) (K : ℝ≥0)
    (hwCont : ContinuousOn w (Icc a c))
    (hDiff : ∀ y ∈ Ioo a c, DifferentiableAt ℝ w y)
    (hDeriv : ∀ y ∈ Ioo a c, ‖deriv w y‖₊ ≤ K) :
    LipschitzOnWith K w (Icc a c) := by sorry
