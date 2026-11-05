-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Martingale_notMem_of_mem
-- name    : ClauseBound.ParityChecks.Martingale.notMem_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:27.903214+00:00
-- url     : https://prove2.me/theorems/569ced10-c76e-4dd6-b2f6-9e1be7787aee
-- title:
--   Martingale: not Mem of mem
-- statement:
--   A clause that is not yet decided for check j is not in check j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L49-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L49-L50

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
omit [Fintype E] [DecidableEq E]

theorem ClauseBound.ParityChecks.Martingale.notMem_of_mem {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) : e ∉ Λ j := by sorry
