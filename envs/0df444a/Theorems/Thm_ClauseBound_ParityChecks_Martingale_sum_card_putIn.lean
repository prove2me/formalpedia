-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Martingale_sum_card_putIn
-- name    : ClauseBound.ParityChecks.Martingale.sum_card_putIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:39.340572+00:00
-- url     : https://prove2.me/theorems/aefe4986-c45b-4fc8-a9f6-2da5982c05db
-- title:
--   Martingale: sum card put In
-- statement:
--   After «in», the checks have one pair more.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L94-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L94-L99

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

theorem ClauseBound.ParityChecks.Martingale.sum_card_putIn {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    ∑ j' ∈ range r, #(putIn j Λ e j') = ∑ j' ∈ range r, #(Λ j') + 1 := by sorry
