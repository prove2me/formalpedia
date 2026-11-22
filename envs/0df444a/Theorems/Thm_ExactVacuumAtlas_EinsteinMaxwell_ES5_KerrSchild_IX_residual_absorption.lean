-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_IX_residual_absorption
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.residual_absorption
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-22T02:14:38.282291+00:00
-- url     : https://prove2.me/theorems/888400a0-d37e-411d-9c68-98b78e529eb4
-- title:
--   Residual absorption bridge
-- statement:
--   Residual absorption bridge
--
--   A residual satisfying an affine contraction bound is bounded by the control term divided by one minus the contraction factor.
--
--   **Scope.** Exact Spacetime Atlas IX analytic bridge for the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. The package records actual-source regularity, solvability equivalence and weighted residual absorption. Metric-valued Ricci correspondence and the implicit-function theorem certificate are later formalization gates. **Attribution.** The local Lean source and the registered B3 definition records are the evidence for these analytic statements.
-- source:
--   He Wang, Exact Spacetime Atlas IX analytic bridge. Local source, commit 8fc44e0bf5f0; Atlas/EinsteinMaxwell/ES5/KerrSchild/IX/Main.lean#L21-L27; SHA-256 667972f4abed6b2bc2e1a1514d62f66e00f09b1125c33265b0b69ec0fe65e074. Registered definitions: mission/PHYSICS_BOUNDARY.md, notes/B3_POLICY.md. Analytic source and residual bridge: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.residual_absorption {r α η : ℝ} (hη : 0 ≤ η) (hη1 : η < 1)
    (hbound : |r| ≤ α + η * |r|) :
    |r| ≤ α / (1 - η) := by sorry
