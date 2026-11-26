-- Prove2me | Theorems.Thm_FD1D_V5_LocalBellman_Normalized_rateIncrement_eq_common
-- name    : FD1D.V5.LocalBellman.Normalized.rateIncrement_eq_common
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:27:02.472521+00:00
-- url     : https://prove2.me/theorems/c234a45c-2a6d-4129-8b29-85b4b207cdcf
-- title:
--   Normalized: rate Increment eq common
-- statement:
--   The Normalized construction uses the rate Increment eq common property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L120-L135
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L120-L135

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized

theorem FD1D.V5.LocalBellman.Normalized.rateIncrement_eq_common
    {s ρ k : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    rateIncrement s ρ (ρ * k) =
      2 * lambda ρ * J s ρ k +
        (1 + lambda ρ) * lambda ρ * J s ρ k ^ 2 := by sorry
