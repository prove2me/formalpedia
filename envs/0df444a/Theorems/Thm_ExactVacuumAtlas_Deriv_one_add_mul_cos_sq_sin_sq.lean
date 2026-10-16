-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Deriv_one_add_mul_cos_sq_sin_sq
-- name    : ExactVacuumAtlas.Deriv.one_add_mul_cos_sq_sin_sq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T19:45:11.41735+00:00
-- url     : https://prove2.me/theorems/e1e14bc3-977f-4265-b969-28df39f75e51
-- title:
--   Derivative of 1 + K cos²t sin²t
-- statement:
--   For all real K and θ: the function t ↦ 1 + K cos²t sin²t has derivative K (2 cos³θ sin θ − 2 cos θ sin³θ) at θ (HasDerivAt).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Controls/ShearDeriv.lean#L13-L19; SHA-256 289482b30b70007ed251428d9febcddfa951f51d54e87520950d81e2b8842664. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
open Real

theorem ExactVacuumAtlas.Deriv.one_add_mul_cos_sq_sin_sq (K θ : ℝ) :
    HasDerivAt (fun t => 1 + K * (cos t ^ 2 * sin t ^ 2))
      (K * (2 * cos θ ^ 3 * sin θ - 2 * cos θ * sin θ ^ 3)) θ := by sorry
