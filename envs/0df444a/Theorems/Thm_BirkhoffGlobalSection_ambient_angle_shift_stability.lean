-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_ambient_angle_shift_stability
-- name    : BirkhoffGlobalSection.ambient_angle_shift_stability
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T17:49:56.211157+00:00
-- url     : https://prove2.me/theorems/edd0d75e-6eee-43fa-b267-c589a41b4c81
-- title:
--   Shift stability of the ambient period increment
-- statement:
--   The ambient increment is stable under shifting the period interval, up to one full turn uniformly in the starting time:
--
--   $$
--   \alpha(a+T)-\alpha(a) \le \alpha(T)-\alpha(0)+2\pi
--   \qquad\text{for every }a.
--   $$
--
--   The variational flow over a shifted period is conjugate to the flow over the base period, so the two ambient increments agree up to the branch choice. This isolates the change-of-initial-time half of the comparison; no vector, frame, or polar angle appears.
-- source:
--   Derived frame and periodic-cocycle estimate for the quaternionic frame and determinant rotation constructions in Joung-van Koert, https://arxiv.org/html/2407.19159v3, Section 2.3, and Gutt, https://arxiv.org/pdf/1307.7239, p. 2, Theorem 1, Eq. (3).

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

open scoped ContDiff

namespace BirkhoffGlobalSection

open scoped ContDiff

theorem ambient_angle_shift_stability
    (F : Phase → ℝ) (S : Set Phase) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn F S x T)
    (hF : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t))
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y)
    (α : ℝ → ℝ) (hα : IsAmbientRotationAngle Y α) :
    ∀ a : ℝ, α (a + T) - α a ≤ α T - α 0 + 2 * Real.pi := by sorry

end BirkhoffGlobalSection
