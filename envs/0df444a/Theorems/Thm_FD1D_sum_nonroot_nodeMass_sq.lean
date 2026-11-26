-- Prove2me | Theorems.Thm_FD1D_sum_nonroot_nodeMass_sq
-- name    : FD1D.sum_nonroot_nodeMass_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:50:24.361539+00:00
-- url     : https://prove2.me/theorems/fc0ebc1c-c7f8-531c-ab4e-bce2628cd2ec
-- title:
--   FD1 D: sum nonroot node Mass sq
-- statement:
--   `∑_{v ≠ root} p_v² = 1 - 1/n` for `n = 2^L`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L698-L710
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L698-L710

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.sum_nonroot_nodeMass_sq (L : ℕ) :
    nonrootMassSqSum L = 1 - 1 / (2 ^ L : ℝ) := by sorry
