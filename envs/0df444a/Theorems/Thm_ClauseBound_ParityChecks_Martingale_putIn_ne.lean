-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Martingale_putIn_ne
-- name    : ClauseBound.ParityChecks.Martingale.putIn_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:03.935684+00:00
-- url     : https://prove2.me/theorems/2969bdf4-f6e5-4df1-901f-a7094ec4902a
-- title:
--   Martingale: put In ne
-- statement:
--   After «in», the other checks are as before.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L40-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L40-L40

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

theorem ClauseBound.ParityChecks.Martingale.putIn_ne {j j' : ℕ} (h : j' ≠ j) (Λ : ℕ → Finset E) (e : E) : putIn j Λ e j' = Λ j' := by sorry
