-- Prove2me | Theorems.Thm_FD1D_stationary_expect_drift_eq_remainder
-- name    : FD1D.stationary_expect_drift_eq_remainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:31.813998+00:00
-- url     : https://prove2.me/theorems/33b3b9b5-b3b1-4abb-bd6f-43d61daa4617
-- title:
--   FD1 D: stationary expect drift eq remainder
-- statement:
--   Explicit finite-state stationarity: `K` has row sum one, `mu K = mu`, and
--   its conditional potential drift is `D-R`.  Then `E_mu D = E_mu R`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L208-L268
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L208-L268

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.stationary_expect_drift_eq_remainder
    {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (K : α → α → ℝ)
    (Phi D R : α → ℝ)
    (hrow : ∀ x, ∑ y, K x y = 1)
    (hstationary : ∀ y, ∑ x, μ.mass x * K x y = μ.mass y)
    (hdrift : ∀ x, ∑ y, K x y * (Phi y - Phi x) = D x - R x) :
    μ.expect D = μ.expect R := by sorry
