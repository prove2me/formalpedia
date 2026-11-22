-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_IX_analytic_actual_source_bridge
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.analytic_actual_source_bridge
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-22T02:14:39.304588+00:00
-- url     : https://prove2.me/theorems/cb0cb1ea-4a52-42e2-856b-3d9e636a7366
-- title:
--   Exact Spacetime Atlas IX analytic actual-source bridge
-- statement:
--   Exact Spacetime Atlas IX compact analytic source/residual bridge
--
--   This release root combines the affine source derivative, weighted residual triangle estimate and scalar residual absorption estimate into one reusable theorem.
--
--   **Scope.** Exact Spacetime Atlas IX compact analytic bridge for affine source derivatives and weighted residual estimates over `ℝ`. The package records the exact Lean statements of the source derivative, residual triangle and scalar absorption lemmas. Metric-valued Ricci correspondence and the implicit-function theorem certificate are later formalization gates.
-- source:
--   He Wang, Exact Spacetime Atlas IX analytic bridge. Local source, commit 8fc44e0bf5f0; Atlas/EinsteinMaxwell/ES5/KerrSchild/IX/Main.lean#L29-L46; SHA-256 667972f4abed6b2bc2e1a1514d62f66e00f09b1125c33265b0b69ec0fe65e074. Registered definitions: mission/PHYSICS_BOUNDARY.md, notes/B3_POLICY.md. Analytic source and residual bridge: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.analytic_actual_source_bridge (a b u v r α η x : ℝ)
    (hη : 0 ≤ η) (hη1 : η < 1)
    (hbound : |r| ≤ α + η * |r|) :
    HasDerivAt (fun t : ℝ => a * t + b) a x ∧
      |a * u + b * v| ≤ |a| * |u| + |b| * |v| ∧
      |r| ≤ α / (1 - η) := by sorry
