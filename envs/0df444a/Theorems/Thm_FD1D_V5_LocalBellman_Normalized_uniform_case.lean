-- Prove2me | Theorems.Thm_FD1D_V5_LocalBellman_Normalized_uniform_case
-- name    : FD1D.V5.LocalBellman.Normalized.uniform_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:27:59.227874+00:00
-- url     : https://prove2.me/theorems/0b0479f4-752c-422b-9247-b4b29ac38a68
-- title:
--   Normalized: uniform case
-- statement:
--   The Normalized construction uses the uniform case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L280-L369
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L280-L369

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized

theorem FD1D.V5.LocalBellman.Normalized.uniform_case
    {s r ρ : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hactive : A s ρ ≤ 8) :
    residual s r ρ (uniform s ρ) ≥
      (rateIncrement s ρ (uniform s ρ) + uniform s ρ ^ 2) / 1000 := by sorry
