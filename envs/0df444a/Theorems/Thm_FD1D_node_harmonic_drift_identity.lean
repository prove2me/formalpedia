-- Prove2me | Theorems.Thm_FD1D_node_harmonic_drift_identity
-- name    : FD1D.node_harmonic_drift_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:03.101838+00:00
-- url     : https://prove2.me/theorems/e66fcc31-c645-4080-b905-9b98f54d1f26
-- title:
--   FD1 D: node harmonic drift identity
-- statement:
--   Exact drift of one node under an independent deletion and arrival.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L32-L38
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L32-L38

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.node_harmonic_drift_identity
    (a N p q : ℝ) (hNa : N + a ≠ 0) (hNa1 : N + a + 1 ≠ 0) :
    p * (1 - q) / (N + a + 1) - q * (1 - p) / (N + a) =
      (p - q) / (N + a) -
        p * (1 - q) / ((N + a) * (N + a + 1)) := by sorry
