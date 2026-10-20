-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleRamseyNumber_log_isTheta
-- name    : ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_log_isTheta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/3d7f9e5d-ed32-4acb-81a1-f7e7f31b52b8
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_log_isTheta
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_log_isTheta :
    (fun k : ℕ => Real.log (triangleRamseyNumber k : ℝ))
      =Θ[atTop] (fun k : ℕ => (k : ℝ) * Real.log (k : ℝ)) := by sorry
