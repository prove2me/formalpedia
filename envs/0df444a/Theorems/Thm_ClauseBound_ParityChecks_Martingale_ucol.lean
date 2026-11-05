-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Martingale_ucol
-- name    : ClauseBound.ParityChecks.Martingale.ucol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:58:57.088886+00:00
-- url     : https://prove2.me/theorems/36805ad0-b789-4854-afd7-61958abea991
-- title:
--   Martingale: ucol
-- statement:
--   One decision, fourth term.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L171-L187
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L171-L187

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

theorem ClauseBound.ParityChecks.Martingale.ucol (nb : ℕ) {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    pr nb * Ucol nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Ucol nb r j Λ (D.erase e) = Ucol nb r j Λ D := by sorry
