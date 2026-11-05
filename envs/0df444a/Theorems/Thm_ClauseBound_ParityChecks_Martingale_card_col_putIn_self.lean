-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Martingale_card_col_putIn_self
-- name    : ClauseBound.ParityChecks.Martingale.card_col_putIn_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:58:49.766383+00:00
-- url     : https://prove2.me/theorems/72762fe0-e381-4bf9-ad52-b9622a699eb2
-- title:
--   Martingale: card col put In self
-- statement:
--   After «in», the clause e is in one check more.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L148-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L148-L157

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

theorem ClauseBound.ParityChecks.Martingale.card_col_putIn_self {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    #{j' ∈ range r | e ∈ putIn j Λ e j'} = #{j' ∈ range r | e ∈ Λ j'} + 1 := by sorry
