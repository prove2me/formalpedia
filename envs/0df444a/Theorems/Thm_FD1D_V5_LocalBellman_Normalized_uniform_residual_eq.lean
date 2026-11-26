-- Prove2me | Theorems.Thm_FD1D_V5_LocalBellman_Normalized_uniform_residual_eq
-- name    : FD1D.V5.LocalBellman.Normalized.uniform_residual_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:27:33.425347+00:00
-- url     : https://prove2.me/theorems/8898eadc-44b7-5fa4-85cc-cf75256238e5
-- title:
--   Normalized: uniform residual eq
-- statement:
--   The Normalized construction uses the uniform residual eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L160-L186
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L160-L186

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized

theorem FD1D.V5.LocalBellman.Normalized.uniform_residual_eq
    {s r ρ : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    residual s r ρ (uniform s ρ) =
      r ^ 2 / 8 - (uniform s ρ) ^ 2 / 24 +
        g s r ^ 2 * (uniform s ρ) ^ 2 /
          (d s ρ * (s + 1 / 2)) +
        g s r * (1 / 2 - r) * (s + 1) /
          (2 * d s ρ * (s + 1 / 2)) := by sorry
