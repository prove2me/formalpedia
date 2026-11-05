-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_g_mul_PbOL_le
-- name    : ClauseBound.ParityChecks.g_mul_PbOL_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:49.73342+00:00
-- url     : https://prove2.me/theorems/32ea2493-425e-427f-a0e6-534184e5917a
-- title:
--   Parity Checks: g mul Pb OL le
-- statement:
--   The Parity Checks construction uses the g mul Pb OL le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L119-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L119-L130

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open PaddedDescent.F PaddedDescent.F.Mark
open Sizes
variable {n Δ : ℕ}

theorem ClauseBound.ParityChecks.g_mul_PbOL_le (hn : 1 ≤ n) (hΔ : 2 ≤ Δ) (K : ℕ) : 3 * K ^ 8 * PbOL K n Δ ≤ 1330 * (n + K ^ 8) * Δ * LD Δ * (LD Δ + Nat.clog 2 n + 1) := by sorry
