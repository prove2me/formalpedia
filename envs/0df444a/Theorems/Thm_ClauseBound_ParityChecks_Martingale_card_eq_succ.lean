-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Martingale_card_eq_succ
-- name    : ClauseBound.ParityChecks.Martingale.card_eq_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:57.310133+00:00
-- url     : https://prove2.me/theorems/d0779de4-558c-41f5-9486-1e31e142d42d
-- title:
--   Martingale: card eq succ
-- statement:
--   D has one clause more than D without e.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L54-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L54-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_Martingale
set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Martingale
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype E]

theorem ClauseBound.ParityChecks.Martingale.card_eq_succ {D : Finset E} {e : E} (he : e ∈ D) : #D = #(D.erase e) + 1 := by sorry
