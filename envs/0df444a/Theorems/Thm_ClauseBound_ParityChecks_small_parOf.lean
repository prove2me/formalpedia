-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_small_parOf
-- name    : ClauseBound.ParityChecks.small_parOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:15.897914+00:00
-- url     : https://prove2.me/theorems/ae6ee9d8-cbc5-4f91-a0b4-4d5970bec9a5
-- title:
--   Parity Checks: small par Of
-- statement:
--   The Parity Checks construction uses the small par Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L98-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L98-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params

theorem ClauseBound.ParityChecks.small_parOf (n Δ m : ℕ) : ∀ i ≤ (parOf n Δ m).i₀, 2 ^ n * m.choose ((parOf n Δ m).nb + 1) * m.choose i ≤ 2 ^ ((parOf n Δ m).β - 2) := by sorry
