-- Prove2me | Theorems.Thm_FD1D_V5_LocalBellman_Normalized_threeCap_case
-- name    : FD1D.V5.LocalBellman.Normalized.threeCap_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:28:04.838656+00:00
-- url     : https://prove2.me/theorems/e56aa299-d309-57b7-8ca5-3f8e8c8fe12c
-- title:
--   Normalized: three Cap case
-- statement:
--   The Normalized construction uses the three Cap case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L1428-L1485
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L1428-L1485

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized

theorem FD1D.V5.LocalBellman.Normalized.threeCap_case
    {s r ρ : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    let z := min (feedback s ρ) (min (uniform s ρ) (floorCap s r ρ))
    residual s r ρ z ≥ (rateIncrement s ρ z + z ^ 2) / 1000 := by sorry
