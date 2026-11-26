-- Prove2me | Theorems.Thm_FD1D_expectedGlobalPotentialChange_eq_drift_sub_remainder
-- name    : FD1D.expectedGlobalPotentialChange_eq_drift_sub_remainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:45.534737+00:00
-- url     : https://prove2.me/theorems/0d2b6dd3-3f1b-5644-a12d-9733a7a22eea
-- title:
--   FD1 D: expected Global Potential Change eq drift sub remainder
-- statement:
--   Exact global identity `E[Delta Phi | state] = D - R`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L95-L121
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L95-L121

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.expectedGlobalPotentialChange_eq_drift_sub_remainder
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    {q : ∀ d, DyadicNode d → ℝ}
    (ha : 0 < a)
    (hzero : ∀ d v, N d v = 0 → q d v = 0) :
    expectedGlobalPotentialChange L a N q =
      potentialDrift L a N q - potentialRemainder L a N q := by sorry
