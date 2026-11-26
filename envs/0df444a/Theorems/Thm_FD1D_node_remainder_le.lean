-- Prove2me | Theorems.Thm_FD1D_node_remainder_le
-- name    : FD1D.node_remainder_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:01.135515+00:00
-- url     : https://prove2.me/theorems/b621639a-1398-4ab3-bc39-7d970cebcdc4
-- title:
--   FD1 D: node remainder le
-- statement:
--   The remainder term is bounded by `p h²` using `p ≤ (N+a)h`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L41-L82
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L41-L82

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.node_remainder_le
    {a N p q h : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hNa : 0 < N + a) (hmajor : p ≤ (N + a) * h) :
    0 ≤ p ^ 3 * (1 - q) / ((N + a) * (N + a + 1)) ∧
      p ^ 3 * (1 - q) / ((N + a) * (N + a + 1)) ≤ p * h ^ 2 := by sorry
