-- Prove2me | Theorems.Thm_FD1D_V5_LocalBellman_Normalized_floor_case
-- name    : FD1D.V5.LocalBellman.Normalized.floor_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:27:49.845611+00:00
-- url     : https://prove2.me/theorems/af85db03-3e5d-5768-a84a-f29de02fdd69
-- title:
--   Normalized: floor case
-- statement:
--   The Normalized construction uses the floor case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L1330-L1395
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L1330-L1395

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
set_option maxHeartbeats 600000

theorem FD1D.V5.LocalBellman.Normalized.floor_case
    {s r ρ : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hactiveU : floorCap s r ρ ≤ uniform s ρ)
    (hactiveF : floorCap s r ρ ≤ feedback s ρ) :
    residual s r ρ (floorCap s r ρ) ≥
      (rateIncrement s ρ (floorCap s r ρ) + floorCap s r ρ ^ 2) /
        1000 := by sorry
