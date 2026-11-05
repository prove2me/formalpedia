-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Approx_choose_card_le
-- name    : ClauseBound.ParityChecks.Approx.choose_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:39.969934+00:00
-- url     : https://prove2.me/theorems/f7ec30a0-8fbe-4f7d-b2cd-8358f2377347
-- title:
--   Approx: choose card le
-- statement:
--   C(|s|, i) ≤ C(|E|, i) for every set s of elements of E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L57-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L57-L58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic
import Definitions.Def_ClauseBound_ParityChecks_Approx
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Approx
open Finset _root_.ParityChecks
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [DecidableEq E]

theorem ClauseBound.ParityChecks.Approx.choose_card_le (s : Finset E) (i : ℕ) : (#s).choose i ≤ (Fintype.card E).choose i := by sorry
