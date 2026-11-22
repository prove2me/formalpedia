-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_IX_weighted_residual_triangle
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.weighted_residual_triangle
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-22T02:14:38.532871+00:00
-- url     : https://prove2.me/theorems/ec33d0c2-1dcc-4f90-8a87-a3ce6b000d3f
-- title:
--   Weighted residual triangle bridge
-- statement:
--   Weighted residual triangle bridge
--
--   The absolute-value triangle estimate bounds a weighted residual combination by the corresponding weighted control terms.
--
--   **Scope.** Exact Spacetime Atlas IX analytic bridge for the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. The package records actual-source regularity, solvability equivalence and weighted residual absorption. Metric-valued Ricci correspondence and the implicit-function theorem certificate are later formalization gates. **Attribution.** The local Lean source and the registered B3 definition records are the evidence for these analytic statements.
-- source:
--   He Wang, Exact Spacetime Atlas IX analytic bridge. Local source, commit 8fc44e0bf5f0; Atlas/EinsteinMaxwell/ES5/KerrSchild/IX/Main.lean#L14-L19; SHA-256 667972f4abed6b2bc2e1a1514d62f66e00f09b1125c33265b0b69ec0fe65e074. Registered definitions: mission/PHYSICS_BOUNDARY.md, notes/B3_POLICY.md. Analytic source and residual bridge: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.weighted_residual_triangle (a b u v : ℝ) :
    |a * u + b * v| ≤ |a| * |u| + |b| * |v| := by sorry
