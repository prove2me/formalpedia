-- Prove2me | Theorems.Thm_FD1D_V5_LocalBellman_Normalized_residual_eq_common
-- name    : FD1D.V5.LocalBellman.Normalized.residual_eq_common
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:26:24.207544+00:00
-- url     : https://prove2.me/theorems/a33a801c-1dcf-429c-a7fb-2aec8dc13759
-- title:
--   Normalized: residual eq common
-- statement:
--   The Normalized construction uses the residual eq common property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L92-L118
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L92-L118

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized

theorem FD1D.V5.LocalBellman.Normalized.residual_eq_common
    {s r ρ k : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    residual s r ρ (ρ * k) =
      r ^ 2 / 8 - lambda ρ * k ^ 2 / 24 +
        g s r * (1 / 2 - r) * (s + 1) /
          (2 * d s ρ * (s + 1 / 2)) +
        lambda ρ * g s r / d s ρ * bracket s r ρ k := by sorry
