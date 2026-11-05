-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Martingale_card_col_putIn_ne
-- name    : ClauseBound.ParityChecks.Martingale.card_col_putIn_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:58:57.227459+00:00
-- url     : https://prove2.me/theorems/f79d1b62-c829-423b-ac8c-bba176fe9a27
-- title:
--   Martingale: card col put In ne
-- statement:
--   After «in», the other clauses are in the same checks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L161-L168
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L161-L168

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

theorem ClauseBound.ParityChecks.Martingale.card_col_putIn_ne (r j : ℕ) (Λ : ℕ → Finset E) {e e' : E} (h : e' ≠ e) :
    #{j' ∈ range r | e' ∈ putIn j Λ e j'} = #{j' ∈ range r | e' ∈ Λ j'} := by sorry
