-- Prove2me | Theorems.Thm_FD1D_finite_time_drift_telescope
-- name    : FD1D.finite_time_drift_telescope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:38.751884+00:00
-- url     : https://prove2.me/theorems/0745c7f1-4cb8-4147-8ae0-1070fef33320
-- title:
--   FD1 D: finite time drift telescope
-- statement:
--   Exact summation of the one-step expected drift identities.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L273-L285
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L273-L285

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.finite_time_drift_telescope
    (T : ℕ) (Phi D R : ℕ → ℝ)
    (hdrift : ∀ t < T, Phi (t + 1) - Phi t = D t - R t) :
    ∑ t ∈ Finset.range T, D t =
      ∑ t ∈ Finset.range T, R t + Phi T - Phi 0 := by sorry
